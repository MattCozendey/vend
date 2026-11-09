import Base
import ../../shared.bend as Shared
import ./shared/text.bend as Texts
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
          Cell.agrees(~ty, ~same, z1, z2),
          Cell.agrees(~ty, ~same, o1, o2)
        )(
          Shared.Bool.and_true_right(
            Cell.agrees.here(~ty, ~same, h1, h2),
            Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
          )(a)
        )
      )(g)
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Con{True{}, r}:
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
          Cell.agrees(~ty, ~same, z1, z2),
          Cell.agrees(~ty, ~same, o1, o2)
        )(
          Shared.Bool.and_true_right(
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_one(ty, same, s, k, x):
  match s k:
    case Tries.tip{} q:
      g => {==}
    case Tries.bin{+h, +z, +o} Nil{}:
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
              Cell.agrees(~ty, ~same, z, Tries.tip{}),
              Cell.agrees(~ty, ~same, o, Tries.tip{})
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Cell.agrees(~ty, ~same, z, Tries.tip{}),
          True{},
          Cell.agrees_tip(~ty, ~same, z)
        ):
          {Bool.and(_, Cell.agrees(~ty, ~same, o, Tries.tip{})) == True{}: Bool}
        Cell.agrees_tip(~ty, ~same, o)
    case Tries.bin{+h, +z, +o} Con{False{}, +r}:
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Tries.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Tries.tip{})
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Tries.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Tries.tip{})
        )(Cell.agrees_one(~ty, ~same, z, r, x)(g))(Cell.agrees_tip(~ty, ~same, o))
      )
    case Tries.bin{+h, +z, +o} Con{True{}, +r}:
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Tries.tip{}),
          Cell.agrees(~ty, ~same, o, Tries.Trie.one(Cell<ty>, r, x))
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Tries.tip{}),
          Cell.agrees(~ty, ~same, o, Tries.Trie.one(Cell<ty>, r, x))
        )(Cell.agrees_tip(~ty, ~same, z))(Cell.agrees_one(~ty, ~same, o, r, x)(g))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Quorums
# -------
# Each member of a list ms votes for at most one choice, as vote(g)(m) says in
# the state g. A choice has a majority when more members vote for it than do
# not. A majority is unique, new votes keep it, and a scan of the members finds
# it: so a holder that learns more votes never sees a decided choice change.

# Votes
# -----

# the vote v is for x
def Quorum.hit(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, B>, x: B) -> Bool:
  match v:
    case None{}:
      False{}
    case Some{b}:
      same(b, x)

# the number of members of ms that vote for x
def Quorum.yes(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +x: B
) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, r}:
      Shared.Nat.add_if(
        Quorum.hit(~B, ~same, vote(g)(m), x),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x)
      )

# the number of members of ms that do not vote for x
def Quorum.no(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +x: B
) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, r}:
      Shared.Nat.add_if(
        Bool.not(Quorum.hit(~B, ~same, vote(g)(m), x)),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x)
      )

# x has a majority of ms: more of them vote for it than do not
def Quorum.has(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  +ms: List<&2, A>,
  +g: V,
  +x: B
) -> Bool:
  Nat.is_lt(
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x),
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x)
  )

# the vote v when it has a majority of ms, else rest
def Quorum.winner.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  ms: List<&2, A>,
  g: V
) -> Maybe<&2, B>:
  match v:
    case None{}:
      rest
    case Some{+b}:
      Bool.pick(Maybe<&2, B>, Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b), Some{b}, rest)

# the first vote of a member of ks that has a majority of ms
def Quorum.winner(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ks: List<&2, A>,
  +ms: List<&2, A>,
  +g: V
) -> Maybe<&2, B>:
  match ks:
    case Nil{}:
      None{}
    case Con{k, r}:
      Quorum.winner.at(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        vote(g)(k),
        Quorum.winner(~A, ~B, ~V, ~vote, ~same, r, ms, g),
        ms,
        g
      )

# the vote v is kept in w: when v is for b, so is w
def Quorum.kept(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, B>, w: Maybe<&2, B>) -> Bool:
  match v:
    case None{}:
      True{}
    case Some{b}:
      Quorum.hit(~B, ~same, w, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# every vote of a member of ms in g is kept in g2
def Quorum.keeps(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +g2: V
) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{+m, r}:
      Bool.and(
        Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m)),
        Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# x is not y, so y is not x
def Quorum.ne_flip.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  back: Bool,
  +x: B,
  y: B,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {back == False{}: Bool}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
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
              Equal.cong(B, Bool, z => same(x, z), y, x, Shared.Eq.sound(~B, ~same, laws, y)(x)(e)),
              Shared.Eq.refl(~B, ~same, laws, x)
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# x is not y, so y is not x
def Quorum.ne_flip(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {same(y, x) == False{}: Bool}:
  Quorum.ne_flip.at(~B, ~same, ~laws, same(y, x), x, y, no, {==})

# a vote for y is not a vote for x, when x is not y
def Quorum.hit_excl(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {
  Quorum.hit(~B, ~same, v, y) == True{}: Bool
} -> {Quorum.hit(~B, ~same, v, x) == False{}: Bool}:
  match v:
    case None{}:
      h => {==}
    case Some{b}:
      h =>
        %Equal.sym(
          B,
          b,
          y,
          Shared.Eq.sound(~B, ~same, laws, b)(y)(h)
        ): {same(_, x) == False{}: Bool}
        Quorum.ne_flip(~B, ~same, ~laws, x, y, no)

# Quorum.yes_le_no for one member, by whether it votes for y (hy) and x (hx)
def Quorum.yes_le_no.at(
  hy: Bool,
  hx: Bool,
  excl: {hy == True{}: Bool} -> {hx == False{}: Bool},
  y: Nat,
  n: Nat,
  ih: {Nat.is_le(y, n) == True{}: Bool}
) -> {Nat.is_le(Shared.Nat.add_if(hy, y), Shared.Nat.add_if(Bool.not(hx), n)) == True{}: Bool}:
  match hy hx:
    case True{} True{}:
      Empty.absurd(
        {Nat.is_le(1n+y, n) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, excl({==})))
      )
    case True{} False{}:
      ih
    case False{} True{}:
      ih
    case False{} False{}:
      Shared.Nat.le_succ(y, n)(ih)

# no more members vote for y than do not vote for x, when x is not y
def Quorum.yes_le_no(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ms: List<&2, A>,
  +g: V,
  +x: B,
  +y: B,
  +no: {same(x, y) == False{}: Bool}
) -> {
  Nat.is_le(
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, y),
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      Quorum.yes_le_no.at(
        Quorum.hit(~B, ~same, vote(g)(m), y),
        Quorum.hit(~B, ~same, vote(g)(m), x),
        Quorum.hit_excl(~B, ~same, ~laws, vote(g)(m), x, y, no),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, y),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.yes_le_no(~A, ~B, ~V, ~vote, ~same, ~laws, r, g, x, y, no)
      )

# Quorum.unique once same(x, y) is known (held)
def Quorum.unique.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  held: Bool,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +y: B,
  +e: {same(x, y) == held: Bool},
  hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  hy: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, y) == True{}: Bool}
) -> {x == y: B}:
  match held:
    case True{}:
      Shared.Eq.sound(~B, ~same, laws, x)(y)(e)
    case False{}:
      +yx = Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      +yy = Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, y)
      +nx = Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      ny = Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, y)
      a = Shared.Nat.le_lt(
        yx,
        ny,
        yy
      )(
        Quorum.yes_le_no(
          ~A,
          ~B,
          ~V,
          ~vote,
          ~same,
          ~laws,
          ms,
          g,
          y,
          x,
          Quorum.ne_flip(~B, ~same, ~laws, x, y, e)
        )
      )(hy)
      b = Shared.Nat.lt_le(
        yx,
        yy,
        nx
      )(a)(Quorum.yes_le_no(~A, ~B, ~V, ~vote, ~same, ~laws, ms, g, x, y, e))
      c = Shared.Nat.lt_le(yx, nx, yx)(b)(Shared.Nat.lt_weak(nx, yx)(hx))
      Empty.absurd(
        {x == y: B},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_lt(yx, yx),
            True{},
            Equal.sym(Bool, Nat.is_lt(yx, yx), False{}, Shared.Nat.lt_irrefl(yx)),
            c
          )
        )
      )

# two choices with a majority of the same members are the same
law Quorum.unique:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for ms: List<&2, A>
  for g: V
  for x: B
  for y: B
  {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, y) == True{}: Bool}
    -> {x == y: B}

def Quorum.unique(member, choice, state, vote, same, laws, ms, g, x, y):
  ms = ms
  g = g
  +x = x
  +y = y
  hx => hy => Quorum.unique.at(
    ~member,
    ~choice,
    ~state,
    ~vote,
    ~same,
    ~laws,
    same(x, y),
    ms,
    g,
    x,
    y,
    {==},
    hx,
    hy
  )

# Quorum.yes_more for one member, whose vote v in g is kept as w in g2
def Quorum.yes_more.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  x: B,
  y: Nat,
  y2: Nat,
  k: {Quorum.kept(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(y, y2) == True{}: Bool}
) -> {
  Nat.is_le(
    Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), y),
    Shared.Nat.add_if(Quorum.hit(~B, ~same, w, x), y2)
  )
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Shared.Nat.le_add_if(Quorum.hit(~B, ~same, u, x), y, y2)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(Shared.Nat.add_if(same(b, x), y), y2) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{c}:
      %Equal.sym(B, c, b, Shared.Eq.sound(~B, ~same, laws, c)(b)(k)):
        {
          Nat.is_le(
            Shared.Nat.add_if(same(b, x), y),
            Shared.Nat.add_if(same(_, x), y2)
          )
            == True{}: Bool
        }
      Shared.Nat.add_if_le(same(b, x), y, y2)(ih)

# Quorum.no_less for one member, whose vote v in g is kept as w in g2
def Quorum.no_less.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  x: B,
  n: Nat,
  n2: Nat,
  k: {Quorum.kept(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(n2, n) == True{}: Bool}
) -> {
  Nat.is_le(
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, w, x)), n2),
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), n)
  )
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Shared.Nat.add_if_le_succ(Bool.not(Quorum.hit(~B, ~same, u, x)), n2, n)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(1n+n2, Shared.Nat.add_if(Bool.not(same(b, x)), n)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{c}:
      %Equal.sym(B, c, b, Shared.Eq.sound(~B, ~same, laws, c)(b)(k)):
        {
          Nat.is_le(
            Shared.Nat.add_if(Bool.not(same(_, x)), n2),
            Shared.Nat.add_if(Bool.not(same(b, x)), n)
          )
            == True{}: Bool
        }
      Shared.Nat.add_if_le(Bool.not(same(b, x)), n2, n)(ih)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# kept votes keep the members that vote for x
def Quorum.yes_more(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ms: List<&2, A>,
  +g: V,
  +g2: V,
  +x: B,
  +k: {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
) -> {
  Nat.is_le(
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x),
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g2, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +kh = Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m))
      kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      Quorum.yes_more.at(
        ~B,
        ~same,
        ~laws,
        vote(g)(m),
        vote(g2)(m),
        x,
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g2, x),
        Shared.Bool.and_true_left(kh, kr)(k),
        Quorum.yes_more(
          ~A,
          ~B,
          ~V,
          ~vote,
          ~same,
          ~laws,
          r,
          g,
          g2,
          x,
          Shared.Bool.and_true_right(kh, kr)(k)
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# kept votes keep the members that do not vote for x from growing
def Quorum.no_less(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ms: List<&2, A>,
  +g: V,
  +g2: V,
  +x: B,
  +k: {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
) -> {
  Nat.is_le(
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g2, x),
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +kh = Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m))
      kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      Quorum.no_less.at(
        ~B,
        ~same,
        ~laws,
        vote(g)(m),
        vote(g2)(m),
        x,
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g2, x),
        Shared.Bool.and_true_left(kh, kr)(k),
        Quorum.no_less(
          ~A,
          ~B,
          ~V,
          ~vote,
          ~same,
          ~laws,
          r,
          g,
          g2,
          x,
          Shared.Bool.and_true_right(kh, kr)(k)
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a majority stays a majority when every vote is kept
law Quorum.has_more:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for ms: List<&2, A>
  for g: V
  for g2: V
  for x: B
  {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g2, x) == True{}: Bool}

def Quorum.has_more(member, choice, state, vote, same, laws, ms, g, g2, x):
  +ms = ms
  +g = g
  +g2 = g2
  +x = x
  +k => h =>
    Shared.Nat.lt_le(
      Quorum.no(~member, ~choice, ~state, ~vote, ~same, ms, g2, x),
      Quorum.yes(~member, ~choice, ~state, ~vote, ~same, ms, g, x),
      Quorum.yes(~member, ~choice, ~state, ~vote, ~same, ms, g2, x)
    )(
      Shared.Nat.le_lt(
        Quorum.no(~member, ~choice, ~state, ~vote, ~same, ms, g2, x),
        Quorum.no(~member, ~choice, ~state, ~vote, ~same, ms, g, x),
        Quorum.yes(~member, ~choice, ~state, ~vote, ~same, ms, g, x)
      )(Quorum.no_less(~member, ~choice, ~state, ~vote, ~same, ~laws, ms, g, g2, x, k))(h)
    )(Quorum.yes_more(~member, ~choice, ~state, ~vote, ~same, ~laws, ms, g, g2, x, k))

# Quorum.has_winner when the vote b was picked or not (held)
def Quorum.has_winner.if(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  held: Bool,
  b: B,
  rest: Maybe<&2, B>,
  ms: List<&2, A>,
  g: V,
  x: B,
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == held: Bool},
  ih: {
    rest == Some{x}: Maybe<&2, B>
  } -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Bool.pick(Maybe<&2, B>, held, Some{b}, rest) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}:
  match held:
    case True{}:
      h =>
        %Shared.Maybe.some_inj(
          B,
          b,
          x,
          h
        ): {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, _) == True{}: Bool}
        eb
    case False{}:
      ih

# Quorum.has_winner at the vote v of a member, with rest the winner after it
def Quorum.has_winner.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  x: B,
  ih: {
    rest == Some{x}: Maybe<&2, B>
  } -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, v, rest, ms, g) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}:
  match v:
    case None{}:
      ih
    case Some{+b}:
      Quorum.has_winner.if(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
        b,
        rest,
        ms,
        g,
        x,
        {==},
        ih
      )

# the winner has a majority
law Quorum.has_winner:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ks: List<&2, A>
  for +ms: List<&2, A>
  for +g: V
  for +x: B
  {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ks, ms, g) == Some{x}: Maybe<&2, B>}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}

def Quorum.has_winner(member, choice, state, vote, same, ks, ms, g, x):
  match ks:
    case Nil{}:
      h => Empty.absurd(
        {Quorum.has(~member, ~choice, ~state, ~vote, ~same, ms, g, x) == True{}: Bool},
        Shared.Maybe.none_ne_some(choice, x, h)
      )
    case Con{k, +r}:
      Quorum.has_winner.at(
        ~member,
        ~choice,
        ~state,
        ~vote,
        ~same,
        vote(g)(k),
        Quorum.winner(~member, ~choice, ~state, ~vote, ~same, r, ms, g),
        ms,
        g,
        x,
        Quorum.has_winner(~member, ~choice, ~state, ~vote, ~same, r, ms, g, x)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the scan goes past a vote b without a majority: b is not x (c)
def Quorum.scan.past(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  c: Bool,
  b: B,
  ms: List<&2, A>,
  g: V,
  x: B,
  yr: Nat,
  ec: {same(b, x) == c: Bool},
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == False{}: Bool},
  hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(c, yr)) == True{}: Bool}
) -> {Nat.is_lt(0n, yr) == True{}: Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_lt(0n, yr) == True{}: Bool}, Shared.Bool.false_ne_true(Equal.trans(
            Bool,
            False{},
            Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
            True{},
            Equal.sym(Bool, Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b), False{}, eb),
            %Equal.sym(B, b, x, Shared.Eq.sound(~B, ~same, laws, b)(x)(ec)): {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, _) == True{}: Bool}
            hx)))
    case False{}:
      pos
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Quorum.scan at a vote b, picked or not (held)
def Quorum.scan.if(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  held: Bool,
  +b: B,
  rest: Maybe<&2, B>,
  ms: List<&2, A>,
  g: V,
  +x: B,
  yr: Nat,
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == held: Bool},
  hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(same(b, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Bool.pick(Maybe<&2, B>, held, Some{b}, rest) == Some{x}: Maybe<&2, B>}:
  match held:
    case True{}:
      %Quorum.unique(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        ~laws,
        ms,
        g,
        b,
        x
      )(eb)(hx): {Some{b} == Some{_}: Maybe<&2, B>}
      {==}
    case False{}:
      ih(
        Quorum.scan.past(
          ~A,
          ~B,
          ~V,
          ~vote,
          ~same,
          ~laws,
          same(b, x),
          b,
          ms,
          g,
          x,
          yr,
          {==},
          eb,
          hx,
          pos
        )
      )

# Quorum.scan at the vote v of a member, with rest the winner after it
def Quorum.scan.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  x: B,
  yr: Nat,
  hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, v, rest, ms, g) == Some{x}: Maybe<&2, B>}:
  match v:
    case None{}:
      ih(pos)
    case Some{+b}:
      Quorum.scan.if(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        ~laws,
        Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
        b,
        rest,
        ms,
        g,
        x,
        yr,
        {==},
        hx,
        pos,
        ih
      )

# a scan of members of which some vote for x finds x, when x has a majority
def Quorum.scan(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ks: List<&2, A>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Nat.is_lt(0n, Quorum.yes(~A, ~B, ~V, ~vote, ~same, ks, g, x)) == True{}: Bool
} -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ks, ms, g) == Some{x}: Maybe<&2, B>}:
  match ks:
    case Nil{}:
      pos => Empty.absurd({None{} == Some{x}: Maybe<&2, B>}, Shared.Bool.false_ne_true(pos))
    case Con{k, +r}:
      pos => Quorum.scan.at(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        ~laws,
        vote(g)(k),
        Quorum.winner(~A, ~B, ~V, ~vote, ~same, r, ms, g),
        ms,
        g,
        x,
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x),
        hx,
        pos,
        Quorum.scan(~A, ~B, ~V, ~vote, ~same, ~laws, r, ms, g, x, hx)
      )

# a choice with a majority is the winner
law Quorum.winner_of:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for ms: List<&2, A>
  for g: V
  for x: B
  {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ms, ms, g) == Some{x}: Maybe<&2, B>}

def Quorum.winner_of(member, choice, state, vote, same, laws, ms, g, x):
  +ms = ms
  +g = g
  +x = x
  +hx =>
    Quorum.scan(
      ~member,
      ~choice,
      ~state,
      ~vote,
      ~same,
      ~laws,
      ms,
      ms,
      g,
      x,
      hx
    )(
      Shared.Nat.lt_pos(
        Quorum.no(~member, ~choice, ~state, ~vote, ~same, ms, g, x),
        Quorum.yes(~member, ~choice, ~state, ~vote, ~same, ms, g, x)
      )(hx)
    )

# One member
# ----------

# the one member of [m] decides alone: its vote wins
law Quorum.winner_one:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for +m: A
  for +g: V
  for +x: B
  {vote(g)(m) == Some{x}: Maybe<&2, B>}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, [m], [m], g) == Some{x}: Maybe<&2, B>}

def Quorum.winner_one(member, choice, state, vote, same, laws, m, g, x):
  +h =>
    %Equal.sym(Maybe<&2, choice>, vote(g)(m), Some{x}, h):
      {
        Quorum.winner.at(
          ~member,
          ~choice,
          ~state,
          ~vote,
          ~same,
          _,
          None{},
          [m],
          g
        )
          == Some{x}: Maybe<&2, choice>
      }
    %Equal.sym(Maybe<&2, choice>, vote(g)(m), Some{x}, h):
      {
        Bool.pick(
          Maybe<&2, choice>,
          Nat.is_lt(
            Shared.Nat.add_if(Bool.not(Quorum.hit(~choice, ~same, _, x)), 0n),
            Shared.Nat.add_if(Quorum.hit(~choice, ~same, _, x), 0n)
          ),
          Some{x},
          None{}
        )
          == Some{x}: Maybe<&2, choice>
      }
    %Equal.sym(Bool, same(x, x), True{}, Shared.Eq.refl(~choice, ~same, laws, x)):
      {
        Bool.pick(
          Maybe<&2, choice>,
          Nat.is_lt(Shared.Nat.add_if(Bool.not(_), 0n), Shared.Nat.add_if(_, 0n)),
          Some{x},
          None{}
        )
          == Some{x}: Maybe<&2, choice>
      }
    {==}

# the one member of [m] has not voted: nothing wins
law Quorum.winner_none:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for +m: A
  for +g: V
  {vote(g)(m) == None{}: Maybe<&2, B>}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, [m], [m], g) == None{}: Maybe<&2, B>}

def Quorum.winner_none(member, choice, state, vote, same, m, g):
  h =>
    %Equal.sym(Maybe<&2, choice>, vote(g)(m), None{}, h):
      {
        Quorum.winner.at(
          ~member,
          ~choice,
          ~state,
          ~vote,
          ~same,
          _,
          None{},
          [m],
          g
        )
          == None{}: Maybe<&2, choice>
      }
    {==}

# Ledgers
# =======
# A ledger holds entries in slots: the requests that writers make, and the
# votes of nodes. Ledgers sync by joining what they hold, so every ledger that
# took in the same entries holds the same state, in any order and any number of
# times (State.join_comm, join_assoc, join_idem). A slot with two different
# entries holds many: the request or the vote in it counts for nothing.
#
# A chain is the list of steps that its owners decided: each takes a request,
# or refuses it as stale. A root chain starts at a request that names its first
# owners. A chain below a root starts at the root's first step that takes a
# request that makes it, with the owners of that step. Each next step is the
# vote of a majority of the owners after the step before it, in the next
# bucket of the chain's votes. So a decision is final: a sync that contradicts
# nothing only adds steps to a chain (State.chain_kept).
#
# What a change Q means is the caller's. A ledger reads of a change only its
# View, compares changes with same, and asks judge for a verdict.

# Names
# -----

# a request: the writer that made it and the ID that the writer gave it. A
# version is the request that made it.
type Id is Data:
  Id{writer: String, request: String}

# a chain: the request that started its root, and its key below the root (none
# for the root itself). Keys below one root are prefix-free.
type Chain is Data:
  Chain{root: Id, sub: Maybe<&2, List<&2, Bool>>}

# what a ledger reads of a change: it starts a root chain with its first
# owners; or it changes the chain on, gives it owners (if any) and, on a root,
# makes the chain below it of that key (if any)
type View is Data:
  View.root{owners: List<&2, String>}
  View.on{chain: Chain, owners: Maybe<&2, List<&2, String>>, makes: Maybe<&2, List<&2, Bool>>}

# a vote for a request: its owners take it, or refuse it as stale
type Vote is Data:
  Vote{id: Id, takes: Bool}

# a request of a change, with its time; or a vote of a node
type Entry<-Q: Data> is Data:
  Entry.ask{id: Id, time: String, ask: Q}
  Entry.vote{vote: Vote}

# Keys
# ----

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Tries.Trie.text(w), Tries.Trie.text(r))

# the key of the chain k
def Chain.key(k: Chain) -> List<&2, Bool>:
  match k:
    case Chain{i, None{}}:
      List.append(&2, Bool, Id.key(i), [False{}])
    case Chain{i, Some{c}}:
      List.append(&2, Bool, Id.key(i), True{} <> c)

# the key of the bucket h: h ones, then a zero
def Height.key(h: Nat) -> List<&2, Bool>:
  match h:
    case 0n:
      [False{}]
    case 1n+p:
      True{} <> Height.key(p)

# the slot of the request i
def Slot.ask(i: Id) -> List<&2, Bool>:
  False{} <> Id.key(i)

# the start of the slots of the votes on the chain k
def Slot.votes(k: Chain) -> List<&2, Bool>:
  True{} <> Chain.key(k)

# the slot of the vote of the node n in the bucket h of the chain k
def Slot.vote(k: Chain, h: Nat, n: String) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.votes(k), List.append(&2, Bool, Height.key(h), Tries.Trie.text(n)))

# Equality
# --------

# a and b are the same request
def Id.is_eq(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same vote
def Vote.is_eq(a: Vote, b: Vote) -> Bool:
  match a b:
    case Vote{i1, k1} Vote{i2, k2}:
      Bool.and(Id.is_eq(i1, i2), Shared.Bool.is_eq(k1, k2))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.ask{i1, t1, q1} Entry.ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.vote{v1} Entry.vote{v2}:
      Vote.is_eq(v1, v2)
    case _ _:
      False{}

# The state
# ---------

# what a ledger of changes Q holds: the cell of each slot
def State(-Q: Data) -> Data:
  Tries.Trie<Cell<Entry<Q>>>

# a ledger that holds nothing yet
def State.empty(~Q: Data) -> State(Q):
  Tries.Trie.new(Cell<Entry<Q>>)

# what a holder of a and of b holds: a sync
def State.join(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q), b: State(Q)) -> State(Q):
  Tries.Trie.union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), a, b)

# what a holder of r lacks of s: what a sync from s to r sends
def State.missing(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), r: State(Q)) -> State(Q):
  Tries.Trie.minus(~Cell<Entry<Q>>, ~Cell.is_eq(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, r)

# no entry of t contradicts one of s
def State.agrees(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), t: State(Q)) -> Bool:
  Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s, t)

# s with the entry e in the slot k
def State.put(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), k: List<&2, Bool>, e: Entry<Q>) -> State(Q):
  State.join(~Q, ~same, s, Tries.Trie.one(Cell<Entry<Q>>, k, one{e}))

# the value of a cell, when every holder agrees on it
def Cell.value(-V: Data, m: Maybe<&2, Cell<V>>) -> Maybe<&2, V>:
  match m:
    case Some{one{e}}:
      Some{e}
    case _:
      None{}

# a request that a ledger holds: its time and change
type Asked<-Q: Data> is Data:
  Asked{time: String, ask: Q}

# the request in the entry m
def Asked.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Asked<Q>>:
  match m:
    case Some{Entry.ask{i, t, q}}:
      Some{Asked{t, q}}
    case _:
      None{}

# the request i, when s holds it
def State.asked(~Q: Data, s: State(Q), i: Id) -> Maybe<&2, Asked<Q>>:
  Asked.of(~Q, Cell.value(Entry<Q>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i))))

# the vote in the entry m
def Vote.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Vote>:
  match m:
    case Some{Entry.vote{v}}:
      Some{v}
    case _:
      None{}

# the vote of the node m in the bucket b: the cells of a bucket's slots, by node
def Bucket.vote(~Q: Data, b: State(Q), m: String) -> Maybe<&2, Vote>:
  Vote.of(~Q, Cell.value(Entry<Q>, Tries.Trie.get(Cell<Entry<Q>>, b, Tries.Trie.text(m))))

# Chains
# ------

# a step of a chain: the request that it decided (its time and change),
# whether it took it, and the owners after it, who decide the next step
type Step<-Q: Data> is Data:
  Step{id: Id, takes: Bool, time: String, ask: Q, owners: List<&2, String>}

# the owners of the step k
def Step.owners(-Q: Data, k: Step<Q>) -> List<&2, String>:
  match k:
    case Step{i, a, t, q, ms}:
      ms

# the request of the step k
def Step.id(-Q: Data, k: Step<Q>) -> Id:
  match k:
    case Step{i, a, t, q, ms}:
      i

# the owners after a step that takes a change of the view v (or not), from ms
def View.owners_of(v: View, takes: Bool, ms: List<&2, String>) -> List<&2, String>:
  match v takes:
    case View.on{c, Some{ns}, m} True{}:
      ns
    case w t:
      ms

# the step to i (taken or not), whose request is r
def Step.asked(
  ~Q: Data,
  ~view: Q -> View,
  ms: List<&2, String>,
  i: Id,
  +k: Bool,
  r: Maybe<&2, Asked<Q>>
) -> Maybe<&2, Step<Q>>:
  match r:
    case None{}:
      None{}
    case Some{Asked{t, +q}}:
      Some{Step{i, k, t, q, View.owners_of(view(q), k, ms)}}

# the step to the winner w of a bucket, after a step whose owners are ms
def Step.won(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  ms: List<&2, String>,
  w: Maybe<&2, Vote>
) -> Maybe<&2, Step<Q>>:
  match w:
    case None{}:
      None{}
    case Some{Vote{+i, +k}}:
      Step.asked(~Q, ~view, ms, i, k, State.asked(~Q, s, i))

# the step after one whose owners are ms: the winner of the bucket b
def Step.next(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +ms: List<&2, String>,
  +b: State(Q)
) -> Maybe<&2, Step<Q>>:
  Step.won(
    ~Q,
    ~view,
    s,
    ms,
    Quorum.winner(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ms, ms, b)
  )

# the step k (if any) and the steps after it, from the buckets of t: the next
# bucket at zero, the ones after it at one
def Chain.walk(~Q: Data, ~view: Q -> View, t: State(Q), +s: State(Q), k: Maybe<&2, Step<Q>>) -> List<&2, Step<Q>>:
  match t k:
    case w None{}:
      []
    case Tries.tip{} Some{st}:
      [st]
    case Tries.bin{h, z, o} Some{+st}:
      st <> Chain.walk(~Q, ~view, o, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z))

# the first step of a root chain whose request has the view v
def Root.view(~Q: Data, v: View, i: Id, t: String, q: Q) -> Maybe<&2, Step<Q>>:
  match v:
    case View.root{ms}:
      Some{Step{i, True{}, t, q, ms}}
    case View.on{c, o, m}:
      None{}

# the first step of a root chain, from the request r that starts it
def Root.of(~Q: Data, ~view: Q -> View, i: Id, r: Maybe<&2, Asked<Q>>) -> Maybe<&2, Step<Q>>:
  match r:
    case Some{Asked{t, +q}}:
      Root.view(~Q, view(q), i, t, q)
    case None{}:
      None{}

# the steps of the root chain of i
def Chain.top(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> List<&2, Step<Q>>:
  Chain.walk(
    ~Q,
    ~view,
    Tries.Trie.under(Cell<Entry<Q>>, s, Slot.votes(Chain{i, None{}})),
    s,
    Root.of(~Q, ~view, i, State.asked(~Q, s, i))
  )

# the change of the view v makes the chain c
def View.makes(v: View, c: List<&2, Bool>) -> Bool:
  match v:
    case View.on{k, o, Some{m}}:
      Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, m, c)
    case _:
      False{}

# the step k takes a request that makes the chain c
def Step.makes(~Q: Data, ~view: Q -> View, k: Step<Q>, c: List<&2, Bool>) -> Bool:
  match k:
    case Step{i, True{}, t, q, ms}:
      View.makes(view(q), c)
    case Step{i, False{}, t, q, ms}:
      False{}

# the first step of xs that takes a request that makes the chain c
def Root.made(
  ~Q: Data,
  ~view: Q -> View,
  xs: List<&2, Step<Q>>,
  +c: List<&2, Bool>
) -> Maybe<&2, Step<Q>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+k, r}:
      Shared.Bool.when(
        Maybe<&2, Step<Q>>,
        Step.makes(~Q, ~view, k, c),
        u => Some{k},
        u => Root.made(~Q, ~view, r, c)
      )

# the first step of the chain k
def Chain.first(~Q: Data, ~view: Q -> View, +s: State(Q), k: Chain) -> Maybe<&2, Step<Q>>:
  match k:
    case Chain{+i, None{}}:
      Root.of(~Q, ~view, i, State.asked(~Q, s, i))
    case Chain{+i, Some{c}}:
      Root.made(~Q, ~view, Chain.top(~Q, ~view, s, i), c)

# the steps of the chain k, in order
def State.chain(~Q: Data, ~view: Q -> View, +s: State(Q), +k: Chain) -> List<&2, Step<Q>>:
  Chain.walk(
    ~Q,
    ~view,
    Tries.Trie.under(Cell<Entry<Q>>, s, Slot.votes(k)),
    s,
    Chain.first(~Q, ~view, s, k)
  )

# Status
# ------

# where a request is. Done: a step decided it, and took it or refused it as
# stale. Pending: no step decided it yet. Refused: it is contradicted. NotSeen:
# the ledger does not hold it.
type Status is Data:
  Status.done{takes: Bool}
  Status.pending{}
  Status.refused{}
  Status.not_seen{}

# the verdict of the step of xs that decided i, if one did
def Steps.verdict(-Q: Data, xs: List<&2, Step<Q>>, +i: Id) -> Maybe<&2, Bool>:
  match xs:
    case Nil{}:
      None{}
    case Con{Step{j, +k, t, q, ms}, r}:
      Shared.Bool.when(Maybe<&2, Bool>, Id.is_eq(j, i), u => Some{k}, u => Steps.verdict(Q, r, i))

# the status of a request, from its verdict m
def Status.of.verdict(m: Maybe<&2, Bool>) -> Status:
  match m:
    case None{}:
      Status.pending{}
    case Some{k}:
      Status.done{k}

# the status of the request i, whose change has the view v
def Status.of.view(~Q: Data, ~view: Q -> View, s: State(Q), v: View, i: Id) -> Status:
  match v:
    case View.root{ms}:
      Status.done{True{}}
    case View.on{c, o, m}:
      Status.of.verdict(Steps.verdict(Q, State.chain(~Q, ~view, s, c), i))

# the status of the request i, whose cell is m
def Status.of(~Q: Data, ~view: Q -> View, s: State(Q), i: Id, m: Maybe<&2, Cell<Entry<Q>>>) -> Status:
  match m:
    case None{}:
      Status.not_seen{}
    case Some{many{}}:
      Status.refused{}
    case Some{one{Entry.ask{j, t, q}}}:
      Status.of.view(~Q, ~view, s, view(q), i)
    case Some{one{Entry.vote{v}}}:
      Status.not_seen{}

# where the request i is
def State.status(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Status:
  Status.of(~Q, ~view, s, i, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)))

# Changes
# -------

# the node n may vote in the bucket h of the chain c, whose owners are ms
def Vote.may(~Q: Data, +n: String, s: State(Q), c: Chain, h: Nat, ms: List<&2, String>) -> Bool:
  Bool.and(
    List.contains(~String, ~String.eq, ms, n),
    Maybe.is_none(&2, Cell<Entry<Q>>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.vote(c, h, n)))
  )

# the verdict on the request q, whose view is v, on the chain whose steps are
# xs: refused when it makes a chain that exists, else judge's (none: wait)
def Vote.verdict(
  ~Q: Data,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  +s: State(Q),
  q: Q,
  v: View,
  xs: List<&2, Step<Q>>
) -> Maybe<&2, Bool>:
  match v:
    case View.on{Chain{r, b}, o, Some{m}}:
      Shared.Bool.when(
        Maybe<&2, Bool>,
        List.is_empty(&2, Step<Q>, State.chain(~Q, ~view, s, Chain{r, Some{m}})),
        u => judge(s, q, xs),
        u => Some{False{}}
      )
    case w:
      judge(s, q, xs)

# s with the vote for i (when held), with the verdict m (none: no vote)
def Vote.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  held: Bool,
  m: Maybe<&2, Bool>,
  s: State(Q),
  k: List<&2, Bool>,
  i: Id
) -> State(Q):
  match held m:
    case True{} Some{v}:
      State.put(~Q, ~same, s, k, Entry.vote{Vote{i, v}})
    case h w:
      s

# s after the node n votes for the request i of q, at the last step of xs,
# which is in the bucket h of the chain c whose steps are all, when it may
def Vote.cast(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  xs: List<&2, Step<Q>>,
  +h: Nat,
  +n: String,
  +s: State(Q),
  +c: Chain,
  +all: List<&2, Step<Q>>,
  +i: Id,
  +q: Q
) -> State(Q):
  match xs:
    case Nil{}:
      s
    case Con{Step{j, k, t, q2, +ms}, Nil{}}:
      Vote.put(
        ~Q,
        ~same,
        Bool.and(Vote.may(~Q, n, s, c, h, ms), Maybe.is_none(&2, Bool, Steps.verdict(Q, all, i))),
        Vote.verdict(~Q, ~view, ~judge, s, q, view(q), all),
        s,
        Slot.vote(c, h, n),
        i
      )
    case Con{x, r}:
      Vote.cast(~Q, ~same, ~view, ~judge, r, 1n+h, n, s, c, all, i, q)

# s after the node n votes for the request i of q, whose view is v
def Vote.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  i: Id,
  q: Q,
  v: View
) -> State(Q):
  match v:
    case View.root{ms}:
      s
    case View.on{+c, o, m}:
      +xs = State.chain(~Q, ~view, s, c)
      Vote.cast(~Q, ~same, ~view, ~judge, xs, 0n, n, s, c, xs, i, q)

# s after the node n took in the request i of q at the time t, whose cell in s
# is m: a request that s holds already changes nothing
def State.ask.fresh(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  +q: Q,
  m: Maybe<&2, Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case Some{x}:
      s
    case None{}:
      Vote.ask(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}),
        i,
        q,
        view(q)
      )

# s, after the node n took in the request i of q at the time t: the request,
# and n's vote on it when n owns its chain and judge gives a verdict
def State.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  q: Q
) -> State(Q):
  State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)))

# s after the node n voted on each request of the cells cs, at the end of its
# chain
def Vote.all(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  cs: List<&2, Cell<Entry<Q>>>,
  +n: String,
  +s: State(Q)
) -> State(Q):
  match cs:
    case Nil{}:
      s
    case Con{one{Entry.ask{+i, t, +q}}, r}:
      Vote.all(~Q, ~same, ~view, ~judge, r, n, Vote.ask(~Q, ~same, ~view, ~judge, n, s, i, q, view(q)))
    case Con{x, r}:
      Vote.all(~Q, ~same, ~view, ~judge, r, n, s)

# s, after the node n voted at the end of each chain that it owns, for the first
# request there that judge gives a verdict on
def State.vote(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q)
) -> State(Q):
  Vote.all(~Q, ~same, ~view, ~judge, Tries.Trie.values(Cell<Entry<Q>>, s), n, s)

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# Id.is_eq is True for a request and itself
def Id.is_eq_refl(a: Id) -> {Id.is_eq(a, a) == True{}: Bool}:
  match a:
    case Id{+w, +r}:
      Shared.Bool.and_both(
        String.eq(w, w),
        String.eq(r, r)
      )(Texts.String.eq_refl(w))(Texts.String.eq_refl(r))

# Id.is_eq is True only for equal requests
def Id.is_eq_sound(a: Id, b: Id) -> {Id.is_eq(a, b) == True{}: Bool} -> {a == b: Id}:
  match a b:
    case Id{+w1, +r1} Id{+w2, +r2}:
      +h =>
        %Texts.String.eq_sound(
          w1,
          w2
        )(Shared.Bool.and_true_left(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Id{w1, r1} == Id{_, r2}: Id}
        %Texts.String.eq_sound(
          r1,
          r2
        )(Shared.Bool.and_true_right(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Id{w1, r1} == Id{w1, _}: Id}
        {==}

# the laws of Id.is_eq
def Id.laws() -> Shared.Eq.Laws(Id, Id.is_eq):
  (Id.is_eq_refl, Id.is_eq_sound)

# Vote.is_eq is True for a vote and itself
def Vote.is_eq_refl(a: Vote) -> {Vote.is_eq(a, a) == True{}: Bool}:
  match a:
    case Vote{+i, +k}:
      Shared.Bool.and_both(
        Id.is_eq(i, i),
        Shared.Bool.is_eq(k, k)
      )(Id.is_eq_refl(i))(Shared.Bool.is_eq_refl(k))

# Vote.is_eq is True only for equal votes
def Vote.is_eq_sound(a: Vote, b: Vote) -> {Vote.is_eq(a, b) == True{}: Bool} -> {a == b: Vote}:
  match a b:
    case Vote{+i1, +k1} Vote{+i2, +k2}:
      +h =>
        %Id.is_eq_sound(
          i1,
          i2
        )(Shared.Bool.and_true_left(Id.is_eq(i1, i2), Shared.Bool.is_eq(k1, k2))(h)):
          {Vote{i1, k1} == Vote{_, k2}: Vote}
        %Shared.Bool.is_eq_sound(
          k1,
          k2
        )(Shared.Bool.and_true_right(Id.is_eq(i1, i2), Shared.Bool.is_eq(k1, k2))(h)):
          {Vote{i1, k1} == Vote{i1, _}: Vote}
        {==}

# the laws of Vote.is_eq
def Vote.laws() -> Shared.Eq.Laws(Vote, Vote.is_eq):
  (Vote.is_eq_refl, Vote.is_eq_sound)

# Entry.is_eq is True for an entry and itself
def Entry.is_eq_refl(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>
) -> {Entry.is_eq(~Q, ~same, a, a) == True{}: Bool}:
  match a:
    case Entry.ask{+i, +t, +q}:
      Shared.Bool.and_both(
        Id.is_eq(i, i),
        Bool.and(String.eq(t, t), same(q, q))
      )(
        Id.is_eq_refl(i)
      )(
        Shared.Bool.and_both(
          String.eq(t, t),
          same(q, q)
        )(Texts.String.eq_refl(t))(Shared.Eq.refl(~Q, ~same, laws, q))
      )
    case Entry.vote{v}:
      Vote.is_eq_refl(v)

# Entry.is_eq is True only for equal entries
def Entry.is_eq_sound(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>,
  b: Entry<Q>
) -> {Entry.is_eq(~Q, ~same, a, b) == True{}: Bool} -> {a == b: Entry<Q>}:
  match a b:
    case Entry.ask{+i1, +t1, +q1} Entry.ask{+i2, +t2, +q2}:
      +h =>
        +r1 = Bool.and(String.eq(t1, t2), same(q1, q2))
        +h1 = Shared.Bool.and_true_right(Id.is_eq(i1, i2), r1)(h)
        %Id.is_eq_sound(i1, i2)(Shared.Bool.and_true_left(Id.is_eq(i1, i2), r1)(h)):
          {Entry.ask{i1, t1, q1} == Entry.ask{_, t2, q2}: Entry<Q>}
        %Texts.String.eq_sound(
          t1,
          t2
        )(Shared.Bool.and_true_left(String.eq(t1, t2), same(q1, q2))(h1)):
          {Entry.ask{i1, t1, q1} == Entry.ask{i1, _, q2}: Entry<Q>}
        %Shared.Eq.sound(
          ~Q,
          ~same,
          laws,
          q1,
          q2
        )(Shared.Bool.and_true_right(String.eq(t1, t2), same(q1, q2))(h1)):
          {Entry.ask{i1, t1, q1} == Entry.ask{i1, t1, _}: Entry<Q>}
        {==}
    case Entry.vote{v1} Entry.vote{v2}:
      h =>
        %Vote.is_eq_sound(v1, v2)(h): {Entry.vote{v1} == Entry.vote{_}: Entry<Q>}
        {==}
    case Entry.ask{p0, p1, p2} Entry.vote{q0}:
      h => Empty.absurd(
        {Entry.ask{p0, p1, p2} == Entry.vote{q0}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.vote{p0} Entry.ask{q0, q1, q2}:
      h => Empty.absurd(
        {Entry.vote{p0} == Entry.ask{q0, q1, q2}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Entry.is_eq, by the laws of same
def Entry.laws(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same)
) -> Shared.Eq.Laws(Entry<Q>, Entry.is_eq(~Q, ~same)):
  (a => Entry.is_eq_refl(~Q, ~same, ~laws, a), a => b => Entry.is_eq_sound(~Q, ~same, ~laws, a, b))

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

# a sync is the same either way round
law State.join_comm:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  for b: State(Q)
  {State.join(~Q, ~same, a, b) == State.join(~Q, ~same, b, a): State(Q)}

def State.join_comm(Q, same, laws, a, b):
  Tries.Trie.union_comm(
    ~Cell<Entry<Q>>,
    ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => y => Cell.join_comm(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x, y)),
    a,
    b
  )

# syncs group either way
law State.join_assoc:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  for b: State(Q)
  for c: State(Q)
  {
    State.join(~Q, ~same, State.join(~Q, ~same, a, b), c)
      == State.join(~Q, ~same, a, State.join(~Q, ~same, b, c)): State(Q)
  }

def State.join_assoc(Q, same, laws, a, b, c):
  Tries.Trie.union_assoc(
    ~Cell<Entry<Q>>,
    ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => y => z => Cell.join_assoc(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x, y, z)),
    a,
    b,
    c
  )

# a sync with itself changes nothing
law State.join_idem:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  {State.join(~Q, ~same, a, a) == a: State(Q)}

def State.join_idem(Q, same, laws, a):
  Tries.Trie.union_idem(
    ~Cell<Entry<Q>>,
    ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => Cell.join_idem(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x)),
    a
  )

# what a sync from s sends to r is enough: r with it is r with all of s
law State.missing_join:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for s: State(Q)
  for r: State(Q)
  {State.join(~Q, ~same, r, State.missing(~Q, ~same, s, r)) == State.join(~Q, ~same, r, s): State(Q)}

def State.missing_join(Q, same, laws, s, r):
  Tries.Trie.union_minus(
    ~Cell<Entry<Q>>,
    ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~Cell.is_eq(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => Cell.join_idem(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x)),
    ~(
      (
        x => Cell.is_eq_refl(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x),
        x => y => Cell.is_eq_sound(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), x, y)
      )
    ),
    s,
    r
  )

# Kept reads
# ----------
# What a holder reads of a cell stays when it syncs with a holder that agrees.

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
  f(Cell.value(V, Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)))
    == Some{w}: Maybe<&2, W>
}:
  match m:
    case None{}:
      ag => h => Empty.absurd(
        {
          f(Cell.value(V, Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)))
            == Some{w}: Maybe<&2, W>
        },
        Shared.Maybe.none_ne_some(W, w, Equal.trans(Maybe<&2, W>, None{}, f(None{}), Some{w}, Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone), h))
      )
    case Some{many{}}:
      ag => h => Empty.absurd(
        {
          f(Cell.value(V, Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)))
            == Some{w}: Maybe<&2, W>
        },
        Shared.Maybe.none_ne_some(W, w, Equal.trans(Maybe<&2, W>, None{}, f(None{}), Some{w}, Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone), h))
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
  f(Cell.value(V, Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)))
    == Some{w}: Maybe<&2, W>
}:
  Cell.through.at(~V, ~W, ~same, ~laws, f, fnone, s, t, k, w, Tries.Trie.get(Cell<V>, s, k), {==})

# the entries at zero of tries that agree agree
def Cell.agrees_zero(
  ~V: Data,
  ~same: V -> V -> Bool,
  h1: Maybe<&2, Cell<V>>,
  h2: Maybe<&2, Cell<V>>,
  +z1: Tries.Trie<Cell<V>>,
  +z2: Tries.Trie<Cell<V>>,
  +o1: Tries.Trie<Cell<V>>,
  +o2: Tries.Trie<Cell<V>>
) -> {
  Cell.agrees(~V, ~same, Tries.bin{h1, z1, o1}, Tries.bin{h2, z2, o2}) == True{}: Bool
} -> {Cell.agrees(~V, ~same, z1, z2) == True{}: Bool}:
  h => Shared.Bool.and_true_left(
    Cell.agrees(~V, ~same, z1, z2),
    Cell.agrees(~V, ~same, o1, o2)
  )(
    Shared.Bool.and_true_right(
      Cell.agrees.here(~V, ~same, h1, h2),
      Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
    )(h)
  )

# the entries at one of tries that agree agree
def Cell.agrees_one_side(
  ~V: Data,
  ~same: V -> V -> Bool,
  h1: Maybe<&2, Cell<V>>,
  h2: Maybe<&2, Cell<V>>,
  +z1: Tries.Trie<Cell<V>>,
  +z2: Tries.Trie<Cell<V>>,
  +o1: Tries.Trie<Cell<V>>,
  +o2: Tries.Trie<Cell<V>>
) -> {
  Cell.agrees(~V, ~same, Tries.bin{h1, z1, o1}, Tries.bin{h2, z2, o2}) == True{}: Bool
} -> {Cell.agrees(~V, ~same, o1, o2) == True{}: Bool}:
  h => Shared.Bool.and_true_right(
    Cell.agrees(~V, ~same, z1, z2),
    Cell.agrees(~V, ~same, o1, o2)
  )(
    Shared.Bool.and_true_right(
      Cell.agrees.here(~V, ~same, h1, h2),
      Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
    )(h)
  )

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
  Cell.agrees(~V, ~same, Tries.Trie.under(Cell<V>, s, p), Tries.Trie.under(Cell<V>, t, p)) == True{}: Bool
}:
  match s t p:
    case Tries.tip{} y q:
      h => {==}
    case Tries.bin{h1, z1, o1} Tries.tip{} q:
      h => Cell.agrees_tip(~V, ~same, Tries.Trie.under(Cell<V>, Tries.bin{h1, z1, o1}, q))
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2} Nil{}:
      h => h
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{False{}, r}:
      h => Cell.agrees_under(~V, ~same, z1, z2, r)(Cell.agrees_zero(~V, ~same, h1, h2, z1, z2, o1, o2)(h))
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{True{}, r}:
      h => Cell.agrees_under(~V, ~same, o1, o2, r)(Cell.agrees_one_side(~V, ~same, h1, h2, z1, z2, o1, o2)(h))

# the vote v of the node m in the bucket b1 stays in b1 and b2, when b2 agrees
# with b1
def Bucket.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +b1: State(Q),
  b2: State(Q),
  +m: String,
  v: Maybe<&2, Vote>,
  e: {Bucket.vote(~Q, b1, m) == v: Maybe<&2, Vote>}
) -> {
  State.agrees(~Q, ~same, b1, b2) == True{}: Bool
} -> {Quorum.kept(~Vote, ~Vote.is_eq, v, Bucket.vote(~Q, State.join(~Q, ~same, b1, b2), m)) == True{}: Bool}:
  match v:
    case None{}:
      ag => {==}
    case Some{x}:
      ag =>
        %Equal.sym(
          Maybe<&2, Vote>,
          Bucket.vote(~Q, State.join(~Q, ~same, b1, b2), m),
          Some{x},
          Cell.through(
            ~Entry<Q>,
            ~Vote,
            ~Entry.is_eq(~Q, ~same),
            ~Entry.laws(~Q, ~same, ~laws),
            u => Vote.of(~Q, u),
            {==},
            b1,
            b2,
            Tries.Trie.text(m),
            x
          )(ag)(e)
        ): {Quorum.kept(~Vote, ~Vote.is_eq, Some{x}, _) == True{}: Bool}
        Vote.is_eq_refl(x)

# every vote of a member of ms in the bucket b1 stays in b1 and b2, when b2
# agrees with b1
def Bucket.keeps(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ms: List<&2, String>,
  +b1: State(Q),
  +b2: State(Q)
) -> {
  State.agrees(~Q, ~same, b1, b2) == True{}: Bool
} -> {
  Quorum.keeps(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ms, b1, State.join(~Q, ~same, b1, b2))
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      ag => {==}
    case Con{+m, +r}:
      +ag => Shared.Bool.and_both(
        Quorum.kept(~Vote, ~Vote.is_eq, Bucket.vote(~Q, b1, m), Bucket.vote(~Q, State.join(~Q, ~same, b1, b2), m)),
        Quorum.keeps(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, r, b1, State.join(~Q, ~same, b1, b2))
      )(
        Bucket.kept(~Q, ~same, ~laws, b1, b2, m, Bucket.vote(~Q, b1, m), {==})(ag)
      )(Bucket.keeps(~Q, ~same, ~laws, r, b1, b2)(ag))

# Step.next_kept once the winner w of the bucket b1 is known
def Step.next_kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +ms: List<&2, String>,
  +b1: State(Q),
  +b2: State(Q),
  -st: Step<Q>,
  w: Maybe<&2, Vote>,
  e: {Quorum.winner(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ms, ms, b1) == w: Maybe<&2, Vote>}
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  State.agrees(~Q, ~same, b1, b2) == True{}: Bool
} -> {
  Step.won(~Q, ~view, s, ms, w) == Some{st}: Maybe<&2, Step<Q>>
} -> {
  Step.next(~Q, ~view, State.join(~Q, ~same, s, t), ms, State.join(~Q, ~same, b1, b2)) == Some{st}: Maybe<&2, Step<Q>>
}:
  match w:
    case None{}:
      ag => agb => h => Empty.absurd(
        {
          Step.next(~Q, ~view, State.join(~Q, ~same, s, t), ms, State.join(~Q, ~same, b1, b2))
            == Some{st}: Maybe<&2, Step<Q>>
        },
        Shared.Maybe.none_ne_some(Step<Q>, st, h)
      )
    case Some{Vote{+i, +k}}:
      ag => agb => h =>
        %Equal.sym(
          Maybe<&2, Vote>,
          Quorum.winner(
            ~String,
            ~Vote,
            ~State(Q),
            ~Bucket.vote(~Q),
            ~Vote.is_eq,
            ms,
            ms,
            State.join(~Q, ~same, b1, b2)
          ),
          Some{Vote{i, k}},
          Quorum.winner_of(
            ~String,
            ~Vote,
            ~State(Q),
            ~Bucket.vote(~Q),
            ~Vote.is_eq,
            ~Vote.laws(),
            ms,
            State.join(~Q, ~same, b1, b2),
            Vote{i, k}
          )(
            Quorum.has_more(
              ~String,
              ~Vote,
              ~State(Q),
              ~Bucket.vote(~Q),
              ~Vote.is_eq,
              ~Vote.laws(),
              ms,
              b1,
              State.join(~Q, ~same, b1, b2),
              Vote{i, k}
            )(Bucket.keeps(~Q, ~same, ~laws, ms, b1, b2)(agb))(
              Quorum.has_winner(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ms, ms, b1, Vote{i, k})(e)
            )
          )
        ): {Step.won(~Q, ~view, State.join(~Q, ~same, s, t), ms, _) == Some{st}: Maybe<&2, Step<Q>>}
        Cell.through(
          ~Entry<Q>,
          ~Step<Q>,
          ~Entry.is_eq(~Q, ~same),
          ~Entry.laws(~Q, ~same, ~laws),
          u => Step.asked(~Q, ~view, ms, i, k, Asked.of(~Q, u)),
          {==},
          s,
          t,
          Slot.ask(i),
          st
        )(ag)(h)

# the step after one whose owners are ms stays in a sync that agrees
def Step.next_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +ms: List<&2, String>,
  +b1: State(Q),
  +b2: State(Q),
  -st: Step<Q>
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  State.agrees(~Q, ~same, b1, b2) == True{}: Bool
} -> {
  Step.next(~Q, ~view, s, ms, b1) == Some{st}: Maybe<&2, Step<Q>>
} -> {
  Step.next(~Q, ~view, State.join(~Q, ~same, s, t), ms, State.join(~Q, ~same, b1, b2)) == Some{st}: Maybe<&2, Step<Q>>
}:
  Step.next_kept.at(
    ~Q,
    ~same,
    ~laws,
    ~view,
    s,
    t,
    ms,
    b1,
    b2,
    st,
    Quorum.winner(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ms, ms, b1),
    {==}
  )

# a walk from no step is empty
def Chain.walk_none(~Q: Data, ~view: Q -> View, t: State(Q), s: State(Q)) -> {Chain.walk(~Q, ~view, t, s, None{}) == []: List<&2, Step<Q>>}:
  match t:
    case Tries.tip{}:
      {==}
    case Tries.bin{h, z, o}:
      {==}

# the walk of a sync, from the step after st, once the next step n1 of s is
# known: it keeps the walk of s, given that the rest (ih) does
def Chain.walk_kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +o: State(Q),
  +o1: State(Q),
  +s: State(Q),
  +t: State(Q),
  +st: Step<Q>,
  +z1: State(Q),
  +z2: State(Q),
  n1: Maybe<&2, Step<Q>>,
  e: {Step.next(~Q, ~view, s, Step.owners(Q, st), z1) == n1: Maybe<&2, Step<Q>>},
  ih: {
    List.take(&2, Step<Q>, Chain.walk(~Q, ~view, o, State.join(~Q, ~same, s, t), n1), List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, n1)))
      == Chain.walk(~Q, ~view, o1, s, n1): List<&2, Step<Q>>
  }
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  State.agrees(~Q, ~same, z1, z2) == True{}: Bool
} -> {
  List.take(
    &2,
    Step<Q>,
    st <> Chain.walk(
      ~Q,
      ~view,
      o,
      State.join(~Q, ~same, s, t),
      Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), State.join(~Q, ~same, z1, z2))
    ),
    1n+List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, n1))
  )
    == st <> Chain.walk(~Q, ~view, o1, s, n1): List<&2, Step<Q>>
}:
  match n1:
    case None{}:
      ag => agz =>
        %Equal.sym(List<&2, Step<Q>>, Chain.walk(~Q, ~view, o1, s, None{}), [], Chain.walk_none(~Q, ~view, o1, s)):
          {
            List.take(
              &2,
              Step<Q>,
              st <> Chain.walk(
                ~Q,
                ~view,
                o,
                State.join(~Q, ~same, s, t),
                Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), State.join(~Q, ~same, z1, z2))
              ),
              1n+List.length(&2, Step<Q>, _)
            )
              == st <> _: List<&2, Step<Q>>
          }
        %Equal.sym(
          List<&2, Step<Q>>,
          List.take(&2, Step<Q>, Chain.walk(~Q, ~view, o, State.join(~Q, ~same, s, t), Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), State.join(~Q, ~same, z1, z2))), 0n),
          [],
          Shared.List.take_zero(Step<Q>, Chain.walk(~Q, ~view, o, State.join(~Q, ~same, s, t), Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), State.join(~Q, ~same, z1, z2))))
        ): {st <> _ == [st]: List<&2, Step<Q>>}
        {==}
    case Some{+st2}:
      ag => agz =>
        %Equal.sym(
          Maybe<&2, Step<Q>>,
          Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), State.join(~Q, ~same, z1, z2)),
          Some{st2},
          Step.next_kept(~Q, ~same, ~laws, ~view, s, t, Step.owners(Q, st), z1, z2, st2)(ag)(agz)(e)
        ):
          {
            List.take(
              &2,
              Step<Q>,
              st <> Chain.walk(~Q, ~view, o, State.join(~Q, ~same, s, t), _),
              1n+List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, Some{st2}))
            )
              == st <> Chain.walk(~Q, ~view, o1, s, Some{st2}): List<&2, Step<Q>>
          }
        %Equal.sym(List<&2, Step<Q>>, List.take(&2, Step<Q>, Chain.walk(~Q, ~view, o, State.join(~Q, ~same, s, t), Some{st2}), List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, Some{st2}))), Chain.walk(~Q, ~view, o1, s, Some{st2}), ih): {st <> _ == st <> Chain.walk(~Q, ~view, o1, s, Some{st2}): List<&2, Step<Q>>}
        {==}

# a sync with nothing changes nothing, the other way round
def Trie.union_tip_sym(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q)) -> {State.join(~Q, ~same, a, Tries.tip{}) == a: State(Q)}:
  Tries.Trie.union_tip(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), a)

# a walk from st of buckets that hold at least one, its first take is st
def Chain.walk_kept.tip(~Q: Data, ~view: Q -> View, t2: State(Q), +u: State(Q), +st: Step<Q>) -> {
  List.take(&2, Step<Q>, Chain.walk(~Q, ~view, t2, u, Some{st}), 1n) == [st]: List<&2, Step<Q>>
}:
  match t2:
    case Tries.tip{}:
      {==}
    case Tries.bin{h, z, o}:
      %Equal.sym(
        List<&2, Step<Q>>,
        List.take(&2, Step<Q>, Chain.walk(~Q, ~view, o, u, Step.next(~Q, ~view, u, Step.owners(Q, st), z)), 0n),
        [],
        Shared.List.take_zero(Step<Q>, Chain.walk(~Q, ~view, o, u, Step.next(~Q, ~view, u, Step.owners(Q, st), z)))
      ): {st <> _ == [st]: List<&2, Step<Q>>}
      {==}

# the walk of the buckets t1 from the step m stays at the start of the walk of
# the buckets of t1 and t2 in a sync of s and t, when t agrees with s and t2
# with t1
def Chain.walk_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  t1: State(Q),
  +t2: State(Q),
  +s: State(Q),
  +t: State(Q),
  m: Maybe<&2, Step<Q>>
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  State.agrees(~Q, ~same, t1, t2) == True{}: Bool
} -> {
  List.take(
    &2,
    Step<Q>,
    Chain.walk(~Q, ~view, State.join(~Q, ~same, t1, t2), State.join(~Q, ~same, s, t), m),
    List.length(&2, Step<Q>, Chain.walk(~Q, ~view, t1, s, m))
  )
    == Chain.walk(~Q, ~view, t1, s, m): List<&2, Step<Q>>
}:
  match t1 t2 m:
    case +w w2 None{}:
      ag => agt =>
        %Equal.sym(List<&2, Step<Q>>, Chain.walk(~Q, ~view, w, s, None{}), [], Chain.walk_none(~Q, ~view, w, s)):
          {
            List.take(&2, Step<Q>, Chain.walk(~Q, ~view, State.join(~Q, ~same, w, w2), State.join(~Q, ~same, s, t), None{}), List.length(&2, Step<Q>, _))
              == _: List<&2, Step<Q>>
          }
        Shared.List.take_zero(Step<Q>, Chain.walk(~Q, ~view, State.join(~Q, ~same, w, w2), State.join(~Q, ~same, s, t), None{}))
    case Tries.tip{} y Some{+st}:
      ag => agt => Chain.walk_kept.tip(~Q, ~view, y, State.join(~Q, ~same, s, t), st)
    case Tries.bin{h1, +z1, +o1} Tries.tip{} Some{+st}:
      +ag => agt =>
        %Trie.union_tip_sym(~Q, ~same, o1):
          {
            List.take(
              &2,
              Step<Q>,
              st <> Chain.walk(~Q, ~view, _, State.join(~Q, ~same, s, t), Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), z1)),
              1n+List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z1)))
            )
              == st <> Chain.walk(~Q, ~view, o1, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z1)): List<&2, Step<Q>>
          }
        %Trie.union_tip_sym(~Q, ~same, z1):
          {
            List.take(
              &2,
              Step<Q>,
              st <> Chain.walk(~Q, ~view, State.join(~Q, ~same, o1, Tries.tip{}), State.join(~Q, ~same, s, t), Step.next(~Q, ~view, State.join(~Q, ~same, s, t), Step.owners(Q, st), _)),
              1n+List.length(&2, Step<Q>, Chain.walk(~Q, ~view, o1, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z1)))
            )
              == st <> Chain.walk(~Q, ~view, o1, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z1)): List<&2, Step<Q>>
          }
        Chain.walk_kept.at(
          ~Q,
          ~same,
          ~laws,
          ~view,
          State.join(~Q, ~same, o1, Tries.tip{}),
          o1,
          s,
          t,
          st,
          z1,
          Tries.tip{},
          Step.next(~Q, ~view, s, Step.owners(Q, st), z1),
          {==},
          Chain.walk_kept(~Q, ~same, ~laws, ~view, o1, Tries.tip{}, s, t, Step.next(~Q, ~view, s, Step.owners(Q, st), z1))(ag)(
            Cell.agrees_tip(~Entry<Q>, ~Entry.is_eq(~Q, ~same), o1)
          )
        )(ag)(Cell.agrees_tip(~Entry<Q>, ~Entry.is_eq(~Q, ~same), z1))
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Some{+st}:
      +ag => +agt =>
        Chain.walk_kept.at(
          ~Q,
          ~same,
          ~laws,
          ~view,
          State.join(~Q, ~same, o1, o2),
          o1,
          s,
          t,
          st,
          z1,
          z2,
          Step.next(~Q, ~view, s, Step.owners(Q, st), z1),
          {==},
          Chain.walk_kept(~Q, ~same, ~laws, ~view, o1, o2, s, t, Step.next(~Q, ~view, s, Step.owners(Q, st), z1))(ag)(
            Cell.agrees_one_side(~Entry<Q>, ~Entry.is_eq(~Q, ~same), h1, h2, z1, z2, o1, o2)(agt)
          )
        )(ag)(Cell.agrees_zero(~Entry<Q>, ~Entry.is_eq(~Q, ~same), h1, h2, z1, z2, o1, o2)(agt))

# Root.made_prefix at a first step k, once it is known to make c or not (hit)
def Root.made_prefix.at(
  ~Q: Data,
  ~view: Q -> View,
  hit: Bool,
  +k: Step<Q>,
  r: List<&2, Step<Q>>,
  r2: List<&2, Step<Q>>,
  +c: List<&2, Bool>,
  -st: Step<Q>,
  rec: {Root.made(~Q, ~view, r, c) == Some{st}: Maybe<&2, Step<Q>>} -> {Root.made(~Q, ~view, r2, c) == Some{st}: Maybe<&2, Step<Q>>}
) -> {
  Shared.Bool.when(Maybe<&2, Step<Q>>, hit, u => Some{k}, u => Root.made(~Q, ~view, r, c)) == Some{st}: Maybe<&2, Step<Q>>
} -> {Shared.Bool.when(Maybe<&2, Step<Q>>, hit, u => Some{k}, u => Root.made(~Q, ~view, r2, c)) == Some{st}: Maybe<&2, Step<Q>>}:
  match hit:
    case True{}:
      h => h
    case False{}:
      h => rec(h)

# the first step of xs that makes the chain c is the first of ys, when ys
# starts with xs
def Root.made_prefix(
  ~Q: Data,
  ~view: Q -> View,
  xs: List<&2, Step<Q>>,
  ys: List<&2, Step<Q>>,
  +c: List<&2, Bool>,
  -st: Step<Q>
) -> {
  Root.made(~Q, ~view, xs, c) == Some{st}: Maybe<&2, Step<Q>>
} -> {
  List.take(&2, Step<Q>, ys, List.length(&2, Step<Q>, xs)) == xs: List<&2, Step<Q>>
} -> {Root.made(~Q, ~view, ys, c) == Some{st}: Maybe<&2, Step<Q>>}:
  match xs ys:
    case Nil{} y:
      h => p => Empty.absurd({Root.made(~Q, ~view, y, c) == Some{st}: Maybe<&2, Step<Q>>}, Shared.Maybe.none_ne_some(Step<Q>, st, h))
    case Con{k, r} Nil{}:
      h => p => Empty.absurd(
        {Root.made(~Q, ~view, [], c) == Some{st}: Maybe<&2, Step<Q>>},
        Shared.Bool.false_ne_true(
          Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, Step<Q>>, Bool, l => List.is_empty(&2, Step<Q>, l), [], k <> r, p))
        )
      )
    case Con{+k, +r} Con{+k2, +r2}:
      h => +p =>
        %Equal.sym(
          Step<Q>,
          k2,
          k,
          Equal.cong(
            List<&2, Step<Q>>,
            Step<Q>,
            l => Maybe.default(&2, Step<Q>, List.head(&2, Step<Q>, l), k),
            k2 <> List.take(&2, Step<Q>, r2, List.length(&2, Step<Q>, r)),
            k <> r,
            p
          )
        ): {Root.made(~Q, ~view, _ <> r2, c) == Some{st}: Maybe<&2, Step<Q>>}
        Root.made_prefix.at(
          ~Q,
          ~view,
          Step.makes(~Q, ~view, k, c),
          k,
          r,
          r2,
          c,
          st,
          hr => Root.made_prefix(~Q, ~view, r, r2, c, st)(hr)(
            Equal.cong(
              List<&2, Step<Q>>,
              List<&2, Step<Q>>,
              l => List.tail(&2, Step<Q>, l),
              k2 <> List.take(&2, Step<Q>, r2, List.length(&2, Step<Q>, r)),
              k <> r,
              p
            )
          )
        )(h)

# a walk of the buckets under p of s from m stays at the start of the walk in
# s and t from mu, when t agrees with s and mu keeps the step of m
def Chain.from_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +p: List<&2, Bool>,
  m: Maybe<&2, Step<Q>>,
  mu: Maybe<&2, Step<Q>>,
  k: @-st: Step<Q> -> {m == Some{st}: Maybe<&2, Step<Q>>} -> {mu == Some{st}: Maybe<&2, Step<Q>>}
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  List.take(
    &2,
    Step<Q>,
    Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), p), State.join(~Q, ~same, s, t), mu),
    List.length(&2, Step<Q>, Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, m))
  )
    == Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, m): List<&2, Step<Q>>
}:
  match m:
    case None{}:
      ag =>
        %Equal.sym(
          List<&2, Step<Q>>,
          Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, None{}),
          [],
          Chain.walk_none(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s)
        ):
          {
            List.take(
              &2,
              Step<Q>,
              Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), p), State.join(~Q, ~same, s, t), mu),
              List.length(&2, Step<Q>, _)
            )
              == _: List<&2, Step<Q>>
          }
        Shared.List.take_zero(
          Step<Q>,
          Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), p), State.join(~Q, ~same, s, t), mu)
        )
    case Some{+st}:
      +ag =>
        %Equal.sym(Maybe<&2, Step<Q>>, mu, Some{st}, k(st)({==})):
          {
            List.take(
              &2,
              Step<Q>,
              Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), p), State.join(~Q, ~same, s, t), _),
              List.length(&2, Step<Q>, Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, Some{st}))
            )
              == Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, Some{st}): List<&2, Step<Q>>
          }
        %Equal.sym(
          State(Q),
          Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), p),
          State.join(~Q, ~same, Tries.Trie.under(Cell<Entry<Q>>, s, p), Tries.Trie.under(Cell<Entry<Q>>, t, p)),
          Tries.Trie.under_union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, t, p)
        ):
          {
            List.take(
              &2,
              Step<Q>,
              Chain.walk(~Q, ~view, _, State.join(~Q, ~same, s, t), Some{st}),
              List.length(&2, Step<Q>, Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, Some{st}))
            )
              == Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s, p), s, Some{st}): List<&2, Step<Q>>
          }
        Chain.walk_kept(
          ~Q,
          ~same,
          ~laws,
          ~view,
          Tries.Trie.under(Cell<Entry<Q>>, s, p),
          Tries.Trie.under(Cell<Entry<Q>>, t, p),
          s,
          t,
          Some{st}
        )(ag)(Cell.agrees_under(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s, t, p)(ag))

# the first step of a root chain stays in a sync that agrees
def Root.of_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -st: Step<Q>
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  Root.of(~Q, ~view, i, State.asked(~Q, s, i)) == Some{st}: Maybe<&2, Step<Q>>
} -> {Root.of(~Q, ~view, i, State.asked(~Q, State.join(~Q, ~same, s, t), i)) == Some{st}: Maybe<&2, Step<Q>>}:
  Cell.through(
    ~Entry<Q>,
    ~Step<Q>,
    ~Entry.is_eq(~Q, ~same),
    ~Entry.laws(~Q, ~same, ~laws),
    u => Root.of(~Q, ~view, i, Asked.of(~Q, u)),
    {==},
    s,
    t,
    Slot.ask(i),
    st
  )

# the first step of a chain stays in a sync that agrees
def Chain.first_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  k: Chain,
  -st: Step<Q>
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  Chain.first(~Q, ~view, s, k) == Some{st}: Maybe<&2, Step<Q>>
} -> {Chain.first(~Q, ~view, State.join(~Q, ~same, s, t), k) == Some{st}: Maybe<&2, Step<Q>>}:
  match k:
    case Chain{+i, None{}}:
      Root.of_kept(~Q, ~same, ~laws, ~view, s, t, i, st)
    case Chain{+i, Some{+c}}:
      +ag => h => Root.made_prefix(
        ~Q,
        ~view,
        Chain.top(~Q, ~view, s, i),
        Chain.top(~Q, ~view, State.join(~Q, ~same, s, t), i),
        c,
        st
      )(h)(
        Chain.from_kept(
          ~Q,
          ~same,
          ~laws,
          ~view,
          s,
          t,
          Slot.votes(Chain{i, None{}}),
          Root.of(~Q, ~view, i, State.asked(~Q, s, i)),
          Root.of(~Q, ~view, i, State.asked(~Q, State.join(~Q, ~same, s, t), i)),
          st2 => e => Root.of_kept(~Q, ~same, ~laws, ~view, s, t, i, st2)(ag)(e)
        )(ag)
      )

# a chain only grows in a sync that contradicts nothing: what a ledger decided
# stays decided
law State.chain_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +k: Chain
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {
      List.take(
        &2,
        Step<Q>,
        State.chain(~Q, ~view, State.join(~Q, ~same, s, t), k),
        List.length(&2, Step<Q>, State.chain(~Q, ~view, s, k))
      )
        == State.chain(~Q, ~view, s, k): List<&2, Step<Q>>
    }

def State.chain_kept(Q, same, laws, view, s, t, k):
  +ag => Chain.from_kept(
    ~Q,
    ~same,
    ~laws,
    ~view,
    s,
    t,
    Slot.votes(k),
    Chain.first(~Q, ~view, s, k),
    Chain.first(~Q, ~view, State.join(~Q, ~same, s, t), k),
    st => e => Chain.first_kept(~Q, ~same, ~laws, ~view, s, t, k, st)(ag)(e)
  )(ag)
