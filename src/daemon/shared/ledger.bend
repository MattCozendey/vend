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

# m, or else what k gives
def Maybe.else(-A: Data, m: Maybe<&2, A>, k: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:
  match m:
    case Some{a}:
      Some{a}
    case None{}:
      k(Unit{})

# the first value that f gives, with x, of an item of xs
def List.first(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> Maybe<&2, B>, xs: List<&2, A>, +x: C) -> Maybe<&2, B>:
  match xs:
    case Nil{}:
      None{}
    case Con{a, r}:
      Maybe.else(B, f(x)(a), u => List.first(~A, ~B, ~C, ~f, r, x))

# the step k, when it takes a request that makes the chain c
def Step.made(~Q: Data, ~view: Q -> View, c: List<&2, Bool>, +k: Step<Q>) -> Maybe<&2, Step<Q>>:
  match k:
    case Step{i, True{}, t, q, ms}:
      Shared.Bool.when(Maybe<&2, Step<Q>>, View.makes(view(q), c), u => Some{k}, u => None{})
    case Step{i, False{}, t, q, ms}:
      None{}

# the first step of xs that takes a request that makes the chain c
def Root.made(~Q: Data, ~view: Q -> View, xs: List<&2, Step<Q>>, +c: List<&2, Bool>) -> Maybe<&2, Step<Q>>:
  List.first(~Step<Q>, ~Step<Q>, ~List<&2, Bool>, ~(c => k => Step.made(~Q, ~view, c, k)), xs, c)

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

# the end of a chain: the height of its last step's bucket, and its owners
type Tip is Data:
  Tip{height: Nat, owners: List<&2, String>}

# the tip of a walk whose first step has the owners ms, and the tip m of the
# walk after it
def Tip.after(ms: List<&2, String>, m: Maybe<&2, Tip>) -> Maybe<&2, Tip>:
  match m:
    case None{}:
      Some{Tip{0n, ms}}
    case Some{Tip{h, ns}}:
      Some{Tip{1n+h, ns}}

# the tip of the walk of t from the step k, by height from t
def Chain.tip(~Q: Data, ~view: Q -> View, t: State(Q), +s: State(Q), k: Maybe<&2, Step<Q>>) -> Maybe<&2, Tip>:
  match t k:
    case w None{}:
      None{}
    case Tries.tip{} Some{st}:
      Some{Tip{0n, Step.owners(Q, st)}}
    case Tries.bin{h, z, o} Some{+st}:
      Tip.after(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s, Step.next(~Q, ~view, s, Step.owners(Q, st), z)))

# the tip of the chain k
def State.tip(~Q: Data, ~view: Q -> View, +s: State(Q), +k: Chain) -> Maybe<&2, Tip>:
  Chain.tip(
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

# the verdict of the step k, when it decided i
def Step.verdict(-Q: Data, i: Id, k: Step<Q>) -> Maybe<&2, Bool>:
  match k:
    case Step{j, +v, t, q, ms}:
      Shared.Bool.when(Maybe<&2, Bool>, Id.is_eq(j, i), u => Some{v}, u => None{})

# the verdict of the step of xs that decided i, if one did
def Steps.verdict(~Q: Data, xs: List<&2, Step<Q>>, +i: Id) -> Maybe<&2, Bool>:
  List.first(~Step<Q>, ~Bool, ~Id, ~(i => k => Step.verdict(Q, i, k)), xs, i)

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
      Status.of.verdict(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))

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

# s after the node n votes for the request i of q, at the tip m of the chain c
# whose steps are xs, when it may
def Vote.cast(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  +n: String,
  +s: State(Q),
  +c: Chain,
  +xs: List<&2, Step<Q>>,
  +i: Id,
  +q: Q,
  m: Maybe<&2, Tip>
) -> State(Q):
  match m:
    case None{}:
      s
    case Some{Tip{+h, ms}}:
      Vote.put(
        ~Q,
        ~same,
        Bool.and(Vote.may(~Q, n, s, c, h, ms), Maybe.is_none(&2, Bool, Steps.verdict(~Q, xs, i))),
        Vote.verdict(~Q, ~view, ~judge, s, q, view(q), xs),
        s,
        Slot.vote(c, h, n),
        i
      )

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
      Vote.cast(~Q, ~same, ~view, ~judge, n, s, c, State.chain(~Q, ~view, s, c), i, q, State.tip(~Q, ~view, s, c))

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

# List.first_prefix at a first item, once what f gives of it (m) is known
def List.first_prefix.at(
  -B: Data,
  m: Maybe<&2, B>,
  k1: Unit -> Maybe<&2, B>,
  k2: Unit -> Maybe<&2, B>,
  -b: B,
  rec: {k1(Unit{}) == Some{b}: Maybe<&2, B>} -> {k2(Unit{}) == Some{b}: Maybe<&2, B>}
) -> {Maybe.else(B, m, k1) == Some{b}: Maybe<&2, B>} -> {Maybe.else(B, m, k2) == Some{b}: Maybe<&2, B>}:
  match m:
    case Some{a}:
      h => h
    case None{}:
      h => rec(h)

# the first value that f gives of an item of xs is the first of ys, when ys
# starts with xs
def List.first_prefix(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~f: C -> A -> Maybe<&2, B>,
  xs: List<&2, A>,
  ys: List<&2, A>,
  +x: C,
  -b: B
) -> {
  List.first(~A, ~B, ~C, ~f, xs, x) == Some{b}: Maybe<&2, B>
} -> {
  List.take(&2, A, ys, List.length(&2, A, xs)) == xs: List<&2, A>
} -> {List.first(~A, ~B, ~C, ~f, ys, x) == Some{b}: Maybe<&2, B>}:
  match xs ys:
    case Nil{} y:
      h => p => Empty.absurd({List.first(~A, ~B, ~C, ~f, y, x) == Some{b}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, b, h))
    case Con{a, r} Nil{}:
      h => p => Empty.absurd(
        {List.first(~A, ~B, ~C, ~f, [], x) == Some{b}: Maybe<&2, B>},
        Shared.Bool.false_ne_true(
          Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, A>, Bool, l => List.is_empty(&2, A, l), [], a <> r, p))
        )
      )
    case Con{+a, +r} Con{+a2, +r2}:
      h => +p =>
        %Equal.sym(
          A,
          a2,
          a,
          Equal.cong(
            List<&2, A>,
            A,
            l => Maybe.default(&2, A, List.head(&2, A, l), a),
            a2 <> List.take(&2, A, r2, List.length(&2, A, r)),
            a <> r,
            p
          )
        ): {List.first(~A, ~B, ~C, ~f, _ <> r2, x) == Some{b}: Maybe<&2, B>}
        List.first_prefix.at(
          B,
          f(x)(a),
          u => List.first(~A, ~B, ~C, ~f, r, x),
          u => List.first(~A, ~B, ~C, ~f, r2, x),
          b,
          hr => List.first_prefix(~A, ~B, ~C, ~f, r, r2, x, b)(hr)(
            Equal.cong(
              List<&2, A>,
              List<&2, A>,
              l => List.tail(&2, A, l),
              a2 <> List.take(&2, A, r2, List.length(&2, A, r)),
              a <> r,
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
      +ag => h => List.first_prefix(
        ~Step<Q>,
        ~Step<Q>,
        ~List<&2, Bool>,
        ~(c => k => Step.made(~Q, ~view, c, k)),
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

# Landing
# -------
# A sole owner's vote at the tip of its chain puts the request on the chain.

# m is none when m, else k, is none
def Maybe.else_none(-A: Data, m: Maybe<&2, A>, k: Unit -> Maybe<&2, A>) -> {Maybe.else(A, m, k) == None{}: Maybe<&2, A>} -> {m == None{}: Maybe<&2, A>}:
  match m:
    case Some{a}:
      h => Empty.absurd({Some{a} == None{}: Maybe<&2, A>}, Shared.Maybe.none_ne_some(A, a, Equal.sym(Maybe<&2, A>, Some{a}, None{}, h)))
    case None{}:
      h => {==}

# k gives none when m, else k, is none
def Maybe.else_none_rest(-A: Data, m: Maybe<&2, A>, k: Unit -> Maybe<&2, A>) -> {Maybe.else(A, m, k) == None{}: Maybe<&2, A>} -> {k(Unit{}) == None{}: Maybe<&2, A>}:
  match m:
    case Some{a}:
      h => Empty.absurd({k(Unit{}) == None{}: Maybe<&2, A>}, Shared.Maybe.none_ne_some(A, a, Equal.sym(Maybe<&2, A>, Some{a}, None{}, h)))
    case None{}:
      h => h

# a step that did not decide i leaves the verdict on i to the steps after it
def Steps.verdict_cons(
  ~Q: Data,
  +i: Id,
  +st: Step<Q>,
  r: List<&2, Step<Q>>
) -> {Step.verdict(Q, i, st) == None{}: Maybe<&2, Bool>} -> {Steps.verdict(~Q, st <> r, i) == Steps.verdict(~Q, r, i): Maybe<&2, Bool>}:
  h =>
    %Equal.sym(Maybe<&2, Bool>, Step.verdict(Q, i, st), None{}, h):
      {Maybe.else(Bool, _, u => Steps.verdict(~Q, r, i)) == Steps.verdict(~Q, r, i): Maybe<&2, Bool>}
    {==}

# the step to i decides i
def Step.verdict_self(-Q: Data, +i: Id, k: Bool, t: String, q: Q, ms: List<&2, String>) -> {
  Step.verdict(Q, i, Step{i, k, t, q, ms}) == Some{k}: Maybe<&2, Bool>
}:
  %Equal.sym(Bool, Id.is_eq(i, i), True{}, Id.is_eq_refl(i)):
    {Shared.Bool.when(Maybe<&2, Bool>, _, u => Some{k}, u => None{}) == Some{k}: Maybe<&2, Bool>}
  {==}

# a walk from a step that decides i gives its verdict on i
def Steps.verdict_first(
  ~Q: Data,
  ~view: Q -> View,
  t: State(Q),
  +s: State(Q),
  +x: Step<Q>,
  +i: Id,
  -k: Bool
) -> {Step.verdict(Q, i, x) == Some{k}: Maybe<&2, Bool>} -> {Steps.verdict(~Q, Chain.walk(~Q, ~view, t, s, Some{x}), i) == Some{k}: Maybe<&2, Bool>}:
  match t:
    case Tries.tip{}:
      h =>
        %Equal.sym(Maybe<&2, Bool>, Step.verdict(Q, i, x), Some{k}, h):
          {Maybe.else(Bool, _, u => Steps.verdict(~Q, [], i)) == Some{k}: Maybe<&2, Bool>}
        {==}
    case Tries.bin{h0, z, o}:
      h =>
        %Equal.sym(Maybe<&2, Bool>, Step.verdict(Q, i, x), Some{k}, h):
          {
            Maybe.else(
              Bool,
              _,
              u => Steps.verdict(~Q, Chain.walk(~Q, ~view, o, s, Step.next(~Q, ~view, s, Step.owners(Q, x), z)), i)
            )
              == Some{k}: Maybe<&2, Bool>
          }
        {==}

# a walk from no step has no tip
def Chain.tip_none(~Q: Data, ~view: Q -> View, t: State(Q), s: State(Q)) -> {Chain.tip(~Q, ~view, t, s, None{}) == None{}: Maybe<&2, Tip>}:
  match t:
    case Tries.tip{}:
      {==}
    case Tries.bin{h, z, o}:
      {==}

# m is not the tip of a first step alone
def Tip.is_up(m: Maybe<&2, Tip>) -> Bool:
  match m:
    case Some{Tip{1n+d, xs}}:
      False{}
    case _:
      True{}

# a tip after a first step has no height zero, unless no step follows it
def Tip.after_zero(ms: List<&2, String>, m: Maybe<&2, Tip>, -ns: List<&2, String>) -> {
  Tip.after(ms, m) == Some{Tip{0n, ns}}: Maybe<&2, Tip>
} -> {m == None{}: Maybe<&2, Tip>}:
  match m:
    case None{}:
      h => {==}
    case Some{Tip{d, xs}}:
      h => Empty.absurd(
        {Some{Tip{d, xs}} == None{}: Maybe<&2, Tip>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Tip>,
            Bool,
            u => Tip.is_up(u),
            Some{Tip{1n+d, xs}},
            Some{Tip{0n, ns}},
            h
          )
        )
      )

# the owners of a tip, if any
def Tip.owners_of(m: Maybe<&2, Tip>) -> List<&2, String>:
  match m:
    case Some{Tip{d, ns}}:
      ns
    case None{}:
      []

# the tip one step lower, if any
def Tip.down(m: Maybe<&2, Tip>) -> Maybe<&2, Tip>:
  match m:
    case Some{Tip{1n+d, ns}}:
      Some{Tip{d, ns}}
    case _:
      None{}

# a first step alone is the tip of its owners
def Tip.after_owners(ms: List<&2, String>, -ns: List<&2, String>) -> {
  Tip.after(ms, None{}) == Some{Tip{0n, ns}}: Maybe<&2, Tip>
} -> {ms == ns: List<&2, String>}:
  h => Equal.cong(Maybe<&2, Tip>, List<&2, String>, u => Tip.owners_of(u), Some{Tip{0n, ms}}, Some{Tip{0n, ns}}, h)

# a tip after a first step, one higher, is the tip of the walk after it
def Tip.after_up(ms: List<&2, String>, m: Maybe<&2, Tip>, -e: Nat, -ns: List<&2, String>) -> {
  Tip.after(ms, m) == Some{Tip{1n+e, ns}}: Maybe<&2, Tip>
} -> {m == Some{Tip{e, ns}}: Maybe<&2, Tip>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{Tip{e, ns}}: Maybe<&2, Tip>},
        Shared.Bool.false_ne_true(
          Equal.sym(
            Bool,
            True{},
            False{},
            Equal.cong(Maybe<&2, Tip>, Bool, u => Tip.is_up(u), Some{Tip{0n, ms}}, Some{Tip{1n+e, ns}}, h)
          )
        )
      )
    case Some{Tip{d, xs}}:
      h => Equal.cong(Maybe<&2, Tip>, Maybe<&2, Tip>, u => Tip.down(u), Some{Tip{1n+d, xs}}, Some{Tip{1n+e, ns}}, h)

# a tip after a first step is a tip
def Tip.after_some(ms: List<&2, String>, m: Maybe<&2, Tip>) -> {Tip.after(ms, m) == None{}: Maybe<&2, Tip>} -> Empty:
  match m:
    case None{}:
      h => Shared.Maybe.none_ne_some(Tip, Tip{0n, ms}, Equal.sym(Maybe<&2, Tip>, Some{Tip{0n, ms}}, None{}, h))
    case Some{Tip{d, xs}}:
      h => Shared.Maybe.none_ne_some(Tip, Tip{1n+d, xs}, Equal.sym(Maybe<&2, Tip>, Some{Tip{1n+d, xs}}, None{}, h))

# a walk from a step has a tip
def Chain.tip_some(~Q: Data, ~view: Q -> View, t: State(Q), +s: State(Q), +x: Step<Q>) -> {
  Chain.tip(~Q, ~view, t, s, Some{x}) == None{}: Maybe<&2, Tip>
} -> Empty:
  match t:
    case Tries.tip{}:
      h => Shared.Maybe.none_ne_some(
        Tip,
        Tip{0n, Step.owners(Q, x)},
        Equal.sym(Maybe<&2, Tip>, Some{Tip{0n, Step.owners(Q, x)}}, None{}, h)
      )
    case Tries.bin{h0, z, o}:
      h => Tip.after_some(
        Step.owners(Q, x),
        Chain.tip(~Q, ~view, o, s, Step.next(~Q, ~view, s, Step.owners(Q, x), z))
      )(h)

# the vote v of the node n, alone in a bucket b at n's key, is n's vote there
def Bucket.vote_one(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +b: State(Q),
  +n: String,
  +v: Vote
) -> {
  Tries.Trie.get(Cell<Entry<Q>>, b, Tries.Trie.text(n)) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Bucket.vote(
    ~Q,
    State.join(~Q, ~same, b, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}})),
    n
  )
    == Some{v}: Maybe<&2, Vote>
}:
  h =>
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Tries.Trie.get(
        Cell<Entry<Q>>,
        State.join(~Q, ~same, b, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}})),
        Tries.Trie.text(n)
      ),
      Tries.Trie.pick(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        Tries.Trie.get(Cell<Entry<Q>>, b, Tries.Trie.text(n)),
        Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}}), Tries.Trie.text(n))
      ),
      Tries.Trie.get_union(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        b,
        Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}}),
        Tries.Trie.text(n)
      )
    ): {Vote.of(~Q, Cell.value(Entry<Q>, _)) == Some{v}: Maybe<&2, Vote>}
    %Equal.sym(Maybe<&2, Cell<Entry<Q>>>, Tries.Trie.get(Cell<Entry<Q>>, b, Tries.Trie.text(n)), None{}, h):
      {
        Vote.of(
          ~Q,
          Cell.value(
            Entry<Q>,
            Tries.Trie.pick(
              ~Cell<Entry<Q>>,
              ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
              _,
              Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}}), Tries.Trie.text(n))
            )
          )
        )
          == Some{v}: Maybe<&2, Vote>
      }
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}}), Tries.Trie.text(n)),
      Some{one{Entry.vote{v}}},
      Tries.Trie.get_one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{v}})
    ): {
      Vote.of(
        ~Q,
        Cell.value(
          Entry<Q>,
          Tries.Trie.pick(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), None{}, _)
        )
      )
        == Some{v}: Maybe<&2, Vote>
    }
    {==}

# the sole owner n's vote for i in the bucket b after st puts i on the walk
def Vote.lands.final(
  ~Q: Data,
  ~view: Q -> View,
  +t2: State(Q),
  +s2: State(Q),
  +st: Step<Q>,
  +n: String,
  +b: State(Q),
  +i: Id,
  +k: Bool,
  +tm: String,
  +q: Q
) -> {
  Step.verdict(Q, i, st) == None{}: Maybe<&2, Bool>
} -> {
  Step.owners(Q, st) == [n]: List<&2, String>
} -> {
  Bucket.vote(~Q, b, n) == Some{Vote{i, k}}: Maybe<&2, Vote>
} -> {
  State.asked(~Q, s2, i) == Some{Asked{tm, q}}: Maybe<&2, Asked<Q>>
} -> {
  Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, t2, s2, Step.next(~Q, ~view, s2, Step.owners(Q, st), b)), i)
    == Some{k}: Maybe<&2, Bool>
}:
  hv => ho => hb => ha =>
    %Equal.sym(
      Maybe<&2, Bool>,
      Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, t2, s2, Step.next(~Q, ~view, s2, Step.owners(Q, st), b)), i),
      Steps.verdict(~Q, Chain.walk(~Q, ~view, t2, s2, Step.next(~Q, ~view, s2, Step.owners(Q, st), b)), i),
      Steps.verdict_cons(~Q, i, st, Chain.walk(~Q, ~view, t2, s2, Step.next(~Q, ~view, s2, Step.owners(Q, st), b)))(hv)
    ): {_ == Some{k}: Maybe<&2, Bool>}
    %Equal.sym(List<&2, String>, Step.owners(Q, st), [n], ho):
      {Steps.verdict(~Q, Chain.walk(~Q, ~view, t2, s2, Step.next(~Q, ~view, s2, _, b)), i) == Some{k}: Maybe<&2, Bool>}
    %Equal.sym(
      Maybe<&2, Vote>,
      Quorum.winner(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, [n], [n], b),
      Some{Vote{i, k}},
      Quorum.winner_one(~String, ~Vote, ~State(Q), ~Bucket.vote(~Q), ~Vote.is_eq, ~Vote.laws(), n, b, Vote{i, k})(hb)
    ): {Steps.verdict(~Q, Chain.walk(~Q, ~view, t2, s2, Step.won(~Q, ~view, s2, [n], _)), i) == Some{k}: Maybe<&2, Bool>}
    %Equal.sym(Maybe<&2, Asked<Q>>, State.asked(~Q, s2, i), Some{Asked{tm, q}}, ha):
      {Steps.verdict(~Q, Chain.walk(~Q, ~view, t2, s2, Step.asked(~Q, ~view, [n], i, k, _)), i) == Some{k}: Maybe<&2, Bool>}
    Steps.verdict_first(
      ~Q,
      ~view,
      t2,
      s2,
      Step{i, k, tm, q, View.owners_of(view(q), k, [n])},
      i,
      k
    )(Step.verdict_self(Q, i, k, tm, q, View.owners_of(view(q), k, [n])))

# Vote.lands from a first step st whose next step n1 of s1 is known, at height 0
def Vote.lands.zero(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  +h0: Maybe<&2, Cell<Entry<Q>>>,
  +z: State(Q),
  +o: State(Q),
  +s1: State(Q),
  +tv: State(Q),
  +n: String,
  +i: Id,
  +k: Bool,
  +st: Step<Q>,
  +tm: String,
  +q: Q,
  n1: Maybe<&2, Step<Q>>
) -> {
  State.asked(~Q, State.join(~Q, ~same, s1, tv), i) == Some{Asked{tm, q}}: Maybe<&2, Asked<Q>>
} -> {
  Tip.after(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, n1)) == Some{Tip{0n, [n]}}: Maybe<&2, Tip>
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, z, Tries.Trie.text(n)) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, o, s1, n1), i) == None{}: Maybe<&2, Bool>
} -> {
  Steps.verdict(
    ~Q,
    Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.bin{h0, z, o}, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(0n), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}),
    i
  )
    == Some{k}: Maybe<&2, Bool>
}:
  match n1:
    case None{}:
      ha => ht => hg => hv =>
        Vote.lands.final(
          ~Q,
          ~view,
          State.join(~Q, ~same, o, Tries.tip{}),
          State.join(~Q, ~same, s1, tv),
          st,
          n,
          State.join(~Q, ~same, z, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{Vote{i, k}}})),
          i,
          k,
          tm,
          q
        )(
          Maybe.else_none(Bool, Step.verdict(Q, i, st), u => Steps.verdict(~Q, Chain.walk(~Q, ~view, o, s1, None{}), i))(hv)
        )(
          Tip.after_owners(
            Step.owners(Q, st),
            [n]
          )(
            Equal.trans(
              Maybe<&2, Tip>,
              Tip.after(Step.owners(Q, st), None{}),
              Tip.after(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, None{})),
              Some{Tip{0n, [n]}},
              Equal.cong(
                Maybe<&2, Tip>,
                Maybe<&2, Tip>,
                m => Tip.after(Step.owners(Q, st), m),
                None{},
                Chain.tip(~Q, ~view, o, s1, None{}),
                Equal.sym(Maybe<&2, Tip>, Chain.tip(~Q, ~view, o, s1, None{}), None{}, Chain.tip_none(~Q, ~view, o, s1))
              ),
              ht
            )
          )
        )(Bucket.vote_one(~Q, ~same, z, n, Vote{i, k})(hg))(ha)
    case Some{+st2}:
      ha => ht => hg => hv => Empty.absurd(
        {
          Steps.verdict(
            ~Q,
            Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.bin{h0, z, o}, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(0n), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}),
            i
          )
            == Some{k}: Maybe<&2, Bool>
        },
        Chain.tip_some(~Q, ~view, o, s1, st2)(Tip.after_zero(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, Some{st2}), [n])(ht))
      )

# Vote.lands from a first step st whose next step n1 of s1 is known, at height
# 1+e, given the lemma for the walk after it (rec)
def Vote.lands.up(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +h0: Maybe<&2, Cell<Entry<Q>>>,
  +z: State(Q),
  +o: State(Q),
  +s1: State(Q),
  +tv: State(Q),
  +n: String,
  +i: Id,
  +k: Bool,
  +e: Nat,
  +st: Step<Q>,
  n1: Maybe<&2, Step<Q>>,
  e1: {Step.next(~Q, ~view, s1, Step.owners(Q, st), z) == n1: Maybe<&2, Step<Q>>},
  rec: @st2: Step<Q> -> {
    Chain.tip(~Q, ~view, o, s1, Some{st2}) == Some{Tip{e, [n]}}: Maybe<&2, Tip>
  } -> {
    Steps.verdict(~Q, Chain.walk(~Q, ~view, o, s1, Some{st2}), i) == None{}: Maybe<&2, Bool>
  } -> {
    Steps.verdict(~Q, Chain.walk(~Q, ~view, State.join(~Q, ~same, o, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st2}), i)
      == Some{k}: Maybe<&2, Bool>
  }
) -> {
  State.agrees(~Q, ~same, s1, tv) == True{}: Bool
} -> {
  Tip.after(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, n1)) == Some{Tip{1n+e, [n]}}: Maybe<&2, Tip>
} -> {
  Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, o, s1, n1), i) == None{}: Maybe<&2, Bool>
} -> {
  Steps.verdict(
    ~Q,
    Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.bin{h0, z, o}, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(1n+e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}),
    i
  )
    == Some{k}: Maybe<&2, Bool>
}:
  match n1:
    case None{}:
      ag => ht => hv => Empty.absurd(
        {
          Steps.verdict(
            ~Q,
            Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.bin{h0, z, o}, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(1n+e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}),
            i
          )
            == Some{k}: Maybe<&2, Bool>
        },
        Shared.Maybe.none_ne_some(
          Tip,
          Tip{e, [n]},
          Equal.trans(
            Maybe<&2, Tip>,
            None{},
            Chain.tip(~Q, ~view, o, s1, None{}),
            Some{Tip{e, [n]}},
            Equal.sym(Maybe<&2, Tip>, Chain.tip(~Q, ~view, o, s1, None{}), None{}, Chain.tip_none(~Q, ~view, o, s1)),
            Tip.after_up(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, None{}), e, [n])(ht)
          )
        )
      )
    case Some{+st2}:
      +ag => ht => +hv =>
        %Equal.sym(
          Maybe<&2, Step<Q>>,
          Step.next(~Q, ~view, State.join(~Q, ~same, s1, tv), Step.owners(Q, st), State.join(~Q, ~same, z, Tries.tip{})),
          Some{st2},
          Step.next_kept(~Q, ~same, ~laws, ~view, s1, tv, Step.owners(Q, st), z, Tries.tip{}, st2)(ag)(
            Cell.agrees_tip(~Entry<Q>, ~Entry.is_eq(~Q, ~same), z)
          )(e1)
        ): {
          Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, State.join(~Q, ~same, o, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), _), i)
            == Some{k}: Maybe<&2, Bool>
        }
        %Equal.sym(
          Maybe<&2, Bool>,
          Steps.verdict(~Q, st <> Chain.walk(~Q, ~view, State.join(~Q, ~same, o, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st2}), i),
          Steps.verdict(~Q, Chain.walk(~Q, ~view, State.join(~Q, ~same, o, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st2}), i),
          Steps.verdict_cons(~Q, i, st, Chain.walk(~Q, ~view, State.join(~Q, ~same, o, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st2}))(
            Maybe.else_none(Bool, Step.verdict(Q, i, st), u => Steps.verdict(~Q, Chain.walk(~Q, ~view, o, s1, Some{st2}), i))(hv)
          )
        ): {_ == Some{k}: Maybe<&2, Bool>}
        rec(st2)(Tip.after_up(Step.owners(Q, st), Chain.tip(~Q, ~view, o, s1, Some{st2}), e, [n])(ht))(
          Maybe.else_none_rest(Bool, Step.verdict(Q, i, st), u => Steps.verdict(~Q, Chain.walk(~Q, ~view, o, s1, Some{st2}), i))(hv)
        )

# the sole owner n's vote for i, at the tip d of the walk of t from st, puts i
# on the walk in a sync that agrees and holds i
def Vote.lands(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  t: State(Q),
  +s1: State(Q),
  +tv: State(Q),
  +n: String,
  +i: Id,
  +k: Bool,
  d: Nat,
  +st: Step<Q>,
  +tm: String,
  +q: Q
) -> {
  State.agrees(~Q, ~same, s1, tv) == True{}: Bool
} -> {
  State.asked(~Q, State.join(~Q, ~same, s1, tv), i) == Some{Asked{tm, q}}: Maybe<&2, Asked<Q>>
} -> {
  Chain.tip(~Q, ~view, t, s1, Some{st}) == Some{Tip{d, [n]}}: Maybe<&2, Tip>
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, t, List.append(&2, Bool, Height.key(d), Tries.Trie.text(n))) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Steps.verdict(~Q, Chain.walk(~Q, ~view, t, s1, Some{st}), i) == None{}: Maybe<&2, Bool>
} -> {
  Steps.verdict(~Q, Chain.walk(~Q, ~view, State.join(~Q, ~same, t, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(d), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}), i)
    == Some{k}: Maybe<&2, Bool>
}:
  match t d:
    case Tries.tip{} 0n:
      ag => ha => ht => hg => hv =>
        Vote.lands.final(
          ~Q,
          ~view,
          Tries.tip{},
          State.join(~Q, ~same, s1, tv),
          st,
          n,
          State.join(~Q, ~same, Tries.tip{}, Tries.Trie.one(Cell<Entry<Q>>, Tries.Trie.text(n), one{Entry.vote{Vote{i, k}}})),
          i,
          k,
          tm,
          q
        )(Maybe.else_none(Bool, Step.verdict(Q, i, st), u => Steps.verdict(~Q, [], i))(hv))(
          Equal.cong(Maybe<&2, Tip>, List<&2, String>, m => Tip.owners_of(m), Some{Tip{0n, Step.owners(Q, st)}}, Some{Tip{0n, [n]}}, ht)
        )(Bucket.vote_one(~Q, ~same, Tries.tip{}, n, Vote{i, k})({==}))(ha)
    case Tries.tip{} 1n+e:
      ag => ha => ht => hg => hv => Empty.absurd(
        {
          Steps.verdict(~Q, Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.tip{}, Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(1n+e), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})), State.join(~Q, ~same, s1, tv), Some{st}), i)
            == Some{k}: Maybe<&2, Bool>
        },
        Shared.Bool.false_ne_true(
          Equal.sym(
            Bool,
            True{},
            False{},
            Equal.cong(Maybe<&2, Tip>, Bool, m => Tip.is_up(m), Some{Tip{0n, Step.owners(Q, st)}}, Some{Tip{1n+e, [n]}}, ht)
          )
        )
      )
    case Tries.bin{+h0, +z, +o} 0n:
      ag => Vote.lands.zero(~Q, ~same, ~view, h0, z, o, s1, tv, n, i, k, st, tm, q, Step.next(~Q, ~view, s1, Step.owners(Q, st), z))
    case Tries.bin{+h0, +z, +o} 1n+e2:
      +e = e2
      +ag => +ha => ht => +hg => hv => Vote.lands.up(
        ~Q,
        ~same,
        ~laws,
        ~view,
        h0,
        z,
        o,
        s1,
        tv,
        n,
        i,
        k,
        e,
        st,
        Step.next(~Q, ~view, s1, Step.owners(Q, st), z),
        {==},
        st2 => ht2 => hv2 => Vote.lands(~Q, ~same, ~laws, ~view, o, s1, tv, n, i, k, e, st2, tm, q)(ag)(ha)(ht2)(hg)(hv2)
      )(ag)(ht)(hv)

# a list that holds a node holds it
def Owners.has(n: String) -> {List.contains(~String, ~String.eq, [n], n) == True{}: Bool}:
  %Equal.sym(Bool, String.eq(n, n), True{}, Texts.String.eq_refl(n)):
    {List.any.if(u => List.contains(~String, ~String.eq, [], n), _) == True{}: Bool}
  {==}

# an entry put at a free slot is there
def State.put_get(~Q: Data, ~same: Q -> Q -> Bool, +s: State(Q), +k: List<&2, Bool>, +e: Entry<Q>) -> {
  Tries.Trie.get(Cell<Entry<Q>>, s, k) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {Tries.Trie.get(Cell<Entry<Q>>, State.put(~Q, ~same, s, k, e), k) == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>}:
  h =>
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Tries.Trie.get(Cell<Entry<Q>>, State.put(~Q, ~same, s, k, e), k),
      Tries.Trie.pick(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        Tries.Trie.get(Cell<Entry<Q>>, s, k),
        Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, k, one{e}), k)
      ),
      Tries.Trie.get_union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, Tries.Trie.one(Cell<Entry<Q>>, k, one{e}), k)
    ): {_ == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>}
    %Equal.sym(Maybe<&2, Cell<Entry<Q>>>, Tries.Trie.get(Cell<Entry<Q>>, s, k), None{}, h):
      {
        Tries.Trie.pick(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), _, Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, k, one{e}), k))
          == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>
      }
    Tries.Trie.get_one(Cell<Entry<Q>>, k, one{e})

# the node n votes for i at the tip of the chain c, when it owns it alone, has
# not voted there, i is not decided yet, and judge gives the verdict k
def Vote.cast_puts(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>,
  +n: String,
  +s: State(Q),
  +c: Chain,
  +i: Id,
  +q: Q,
  +h: Nat,
  +k: Bool
) -> {
  State.tip(~Q, ~view, s, c) == Some{Tip{h, [n]}}: Maybe<&2, Tip>
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, s, Slot.vote(c, h, n)) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i) == None{}: Maybe<&2, Bool>
} -> {
  Vote.verdict(~Q, ~view, ~judge, s, q, view(q), State.chain(~Q, ~view, s, c)) == Some{k}: Maybe<&2, Bool>
} -> {
  Vote.cast(~Q, ~same, ~view, ~judge, n, s, c, State.chain(~Q, ~view, s, c), i, q, State.tip(~Q, ~view, s, c))
    == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)
}:
  ht => hg => hv => hj =>
    %Equal.sym(Maybe<&2, Tip>, State.tip(~Q, ~view, s, c), Some{Tip{h, [n]}}, ht):
      {
        Vote.cast(~Q, ~same, ~view, ~judge, n, s, c, State.chain(~Q, ~view, s, c), i, q, _)
          == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)
      }
    %Equal.sym(Bool, List.contains(~String, ~String.eq, [n], n), True{}, Owners.has(n)):
      {
        Vote.put(
          ~Q,
          ~same,
          Bool.and(
            Bool.and(_, Maybe.is_none(&2, Cell<Entry<Q>>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.vote(c, h, n)))),
            Maybe.is_none(&2, Bool, Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))
          ),
          Vote.verdict(~Q, ~view, ~judge, s, q, view(q), State.chain(~Q, ~view, s, c)),
          s,
          Slot.vote(c, h, n),
          i
        )
          == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)
      }
    %Equal.sym(Maybe<&2, Cell<Entry<Q>>>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.vote(c, h, n)), None{}, hg):
      {
        Vote.put(
          ~Q,
          ~same,
          Bool.and(
            Maybe.is_none(&2, Cell<Entry<Q>>, _),
            Maybe.is_none(&2, Bool, Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))
          ),
          Vote.verdict(~Q, ~view, ~judge, s, q, view(q), State.chain(~Q, ~view, s, c)),
          s,
          Slot.vote(c, h, n),
          i
        )
          == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)
      }
    %Equal.sym(Maybe<&2, Bool>, Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i), None{}, hv):
      {
        Vote.put(
          ~Q,
          ~same,
          Maybe.is_none(&2, Bool, _),
          Vote.verdict(~Q, ~view, ~judge, s, q, view(q), State.chain(~Q, ~view, s, c)),
          s,
          Slot.vote(c, h, n),
          i
        )
          == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)
      }
    %Equal.sym(Maybe<&2, Bool>, Vote.verdict(~Q, ~view, ~judge, s, q, view(q), State.chain(~Q, ~view, s, c)), Some{k}, hj):
      {Vote.put(~Q, ~same, True{}, _, s, Slot.vote(c, h, n), i) == State.put(~Q, ~same, s, Slot.vote(c, h, n), Entry.vote{Vote{i, k}}): State(Q)}
    {==}

# Ask.decided once the first step m of the chain c of s1 is known
def Ask.decided.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s1: State(Q),
  +n: String,
  +i: Id,
  +t: String,
  +q: Q,
  +c: Chain,
  +h: Nat,
  +k: Bool,
  m: Maybe<&2, Step<Q>>,
  e: {Chain.first(~Q, ~view, s1, c) == m: Maybe<&2, Step<Q>>}
) -> {
  State.agrees(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})) == True{}: Bool
} -> {
  State.asked(~Q, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), i) == Some{Asked{t, q}}: Maybe<&2, Asked<Q>>
} -> {
  Chain.tip(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1, m) == Some{Tip{h, [n]}}: Maybe<&2, Tip>
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, s1, Slot.vote(c, h, n)) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Steps.verdict(~Q, Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1, m), i) == None{}: Maybe<&2, Bool>
} -> {
  Steps.verdict(~Q, State.chain(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), c), i) == Some{k}: Maybe<&2, Bool>
}:
  match m:
    case None{}:
      ag => ha => ht => hg => hv => Empty.absurd(
        {Steps.verdict(~Q, State.chain(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), c), i) == Some{k}: Maybe<&2, Bool>},
        Shared.Maybe.none_ne_some(
          Tip,
          Tip{h, [n]},
          Equal.trans(
            Maybe<&2, Tip>,
            None{},
            Chain.tip(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1, None{}),
            Some{Tip{h, [n]}},
            Equal.sym(Maybe<&2, Tip>, Chain.tip(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1, None{}), None{}, Chain.tip_none(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1)),
            ht
          )
        )
      )
    case Some{+st}:
      +ag => ha => ht => hg => hv =>
        %Equal.sym(
          Maybe<&2, Step<Q>>,
          Chain.first(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), c),
          Some{st},
          Chain.first_kept(~Q, ~same, ~laws, ~view, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), c, st)(ag)(e)
        ): {
          Steps.verdict(~Q, Chain.walk(~Q, ~view, Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Slot.votes(c)), State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), _), i) == Some{k}: Maybe<&2, Bool>
        }
        %Equal.sym(
          State(Q),
          Tries.Trie.under(Cell<Entry<Q>>, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Slot.votes(c)),
          State.join(~Q, ~same, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), Tries.Trie.under(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), Slot.votes(c))),
          Tries.Trie.under_union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), Slot.votes(c))
        ): {Steps.verdict(~Q, Chain.walk(~Q, ~view, _, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Some{st}), i) == Some{k}: Maybe<&2, Bool>}
        %Equal.sym(
          State(Q),
          Tries.Trie.under(Cell<Entry<Q>>, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), Slot.votes(c)),
          Tries.Trie.one(Cell<Entry<Q>>, List.append(&2, Bool, Height.key(h), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}}),
          Tries.Trie.under_one(Cell<Entry<Q>>, Slot.votes(c), List.append(&2, Bool, Height.key(h), Tries.Trie.text(n)), one{Entry.vote{Vote{i, k}}})
        ): {
          Steps.verdict(~Q, Chain.walk(~Q, ~view, State.join(~Q, ~same, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), _), State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Some{st}), i) == Some{k}: Maybe<&2, Bool>
        }
        Vote.lands(~Q, ~same, ~laws, ~view, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), n, i, k, h, st, t, q)(ag)(ha)(ht)(
          Equal.trans(
            Maybe<&2, Cell<Entry<Q>>>,
            Tries.Trie.get(Cell<Entry<Q>>, Tries.Trie.under(Cell<Entry<Q>>, s1, Slot.votes(c)), List.append(&2, Bool, Height.key(h), Tries.Trie.text(n))),
            Tries.Trie.get(Cell<Entry<Q>>, s1, Slot.vote(c, h, n)),
            None{},
            Tries.Trie.get_under(Cell<Entry<Q>>, s1, Slot.votes(c), List.append(&2, Bool, Height.key(h), Tries.Trie.text(n))),
            hg
          )
        )(hv)

# the sole owner n of the tip of a chain, after it takes in a request there
# that is not decided yet and on which judge gives the verdict k, has decided
# it with the verdict k
def Ask.decided(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s1: State(Q),
  +n: String,
  +i: Id,
  +t: String,
  +q: Q,
  +c: Chain,
  o: Maybe<&2, List<&2, String>>,
  mk: Maybe<&2, List<&2, Bool>>,
  +h: Nat,
  +k: Bool
) -> {
  view(q) == View.on{c, o, mk}: View
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, s1, Slot.ask(i)) == Some{one{Entry.ask{i, t, q}}}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  State.tip(~Q, ~view, s1, c) == Some{Tip{h, [n]}}: Maybe<&2, Tip>
} -> {
  Tries.Trie.get(Cell<Entry<Q>>, s1, Slot.vote(c, h, n)) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Steps.verdict(~Q, State.chain(~Q, ~view, s1, c), i) == None{}: Maybe<&2, Bool>
} -> {
  State.status(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), i) == Status.done{k}: Status
}:
  hq => hask => ht => +hg => hv =>
    +ag = Cell.agrees_one(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s1, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})(hg)
    +hask2 = Cell.agrees_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}}), Slot.ask(i), Entry.ask{i, t, q})(ag)(hask)
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Tries.Trie.get(Cell<Entry<Q>>, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Slot.ask(i)),
      Some{one{Entry.ask{i, t, q}}},
      hask2
    ): {Status.of(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), i, _) == Status.done{k}: Status}
    %Equal.sym(View, view(q), View.on{c, o, mk}, hq): {Status.of.view(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), _, i) == Status.done{k}: Status}
    %Equal.sym(
      Maybe<&2, Bool>,
      Steps.verdict(~Q, State.chain(~Q, ~view, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), c), i),
      Some{k},
      Ask.decided.at(~Q, ~same, ~laws, ~view, s1, n, i, t, q, c, h, k, Chain.first(~Q, ~view, s1, c), {==})(ag)(
        Equal.cong(
          Maybe<&2, Cell<Entry<Q>>>,
          Maybe<&2, Asked<Q>>,
          m => Asked.of(~Q, Cell.value(Entry<Q>, m)),
          Tries.Trie.get(Cell<Entry<Q>>, State.join(~Q, ~same, s1, Tries.Trie.one(Cell<Entry<Q>>, Slot.vote(c, h, n), one{Entry.vote{Vote{i, k}}})), Slot.ask(i)),
          Some{one{Entry.ask{i, t, q}}},
          hask2
        )
      )(ht)(hg)(hv)
    ): {Status.of.verdict(_) == Status.done{k}: Status}
    {==}

# a node that owns the tip of a chain alone decides a request at once when it
# takes it in: when judge gives the verdict k there, the request is done with
# k
law State.ask_decides:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~judge: State(Q) -> Q -> List<&2, Step<Q>> -> Maybe<&2, Bool>
  for +n: String
  for +s: State(Q)
  for +i: Id
  for +t: String
  for +q: Q
  for +c: Chain
  for o: Maybe<&2, List<&2, String>>
  for mk: Maybe<&2, List<&2, Bool>>
  for +h: Nat
  for +k: Bool
  {Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)) == None{}: Maybe<&2, Cell<Entry<Q>>>}
    -> {view(q) == View.on{c, o, mk}: View}
    -> {
      State.tip(~Q, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c)
        == Some{Tip{h, [n]}}: Maybe<&2, Tip>
    }
    -> {
      Tries.Trie.get(Cell<Entry<Q>>, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), Slot.vote(c, h, n))
        == None{}: Maybe<&2, Cell<Entry<Q>>>
    }
    -> {
      Steps.verdict(~Q, State.chain(~Q, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c), i)
        == None{}: Maybe<&2, Bool>
    }
    -> {
      Vote.verdict(
        ~Q,
        ~view,
        ~judge,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}),
        q,
        view(q),
        State.chain(~Q, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c)
      )
        == Some{k}: Maybe<&2, Bool>
    }
    -> {State.status(~Q, ~view, State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q), i) == Status.done{k}: Status}

def State.ask_decides(Q, same, laws, view, judge, n, s, i, t, q, c, o, mk, h, k):
  +h1 => +h2 => +ht => +hg => +hv => hj =>
    %Equal.sym(Maybe<&2, Cell<Entry<Q>>>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)), None{}, h1):
      {State.status(~Q, ~view, State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, _), i) == Status.done{k}: Status}
    %Equal.sym(View, view(q), View.on{c, o, mk}, h2):
      {
        State.status(~Q, ~view, Vote.ask(~Q, ~same, ~view, ~judge, n, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), i, q, _), i)
          == Status.done{k}: Status
      }
    %Equal.sym(
      State(Q),
      Vote.cast(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}),
        c,
        State.chain(~Q, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c),
        i,
        q,
        State.tip(~Q, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c)
      ),
      State.put(~Q, ~same, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), Slot.vote(c, h, n), Entry.vote{Vote{i, k}}),
      Vote.cast_puts(~Q, ~same, ~view, ~judge, n, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), c, i, q, h, k)(ht)(hg)(hv)(hj)
    ): {State.status(~Q, ~view, _, i) == Status.done{k}: Status}
    Ask.decided(~Q, ~same, ~laws, ~view, State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}), n, i, t, q, c, o, mk, h, k)(h2)(
      State.put_get(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q})(h1)
    )(ht)(hg)(hv)

# Answers kept
# ------------

# the verdict of a status, if it is done
def Status.verdict(st: Status) -> Maybe<&2, Bool>:
  match st:
    case Status.done{k}:
      Some{k}
    case _:
      None{}

# st is refused
def Status.is_refused(st: Status) -> Bool:
  match st:
    case Status.refused{}:
      True{}
    case _:
      False{}

# the verdict of the status of a verdict m is m
def Status.verdict_of(m: Maybe<&2, Bool>) -> {Status.verdict(Status.of.verdict(m)) == m: Maybe<&2, Bool>}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

# a status that is not done is not done with k
def Status.not_done(st: Status, -k: Bool) -> {Status.verdict(st) == None{}: Maybe<&2, Bool>} -> {st == Status.done{k}: Status} -> Empty:
  h => d => Shared.Maybe.none_ne_some(
    Bool,
    k,
    Equal.trans(
      Maybe<&2, Bool>,
      None{},
      Status.verdict(st),
      Some{k},
      Equal.sym(Maybe<&2, Bool>, Status.verdict(st), None{}, h),
      Equal.cong(Status, Maybe<&2, Bool>, x => Status.verdict(x), st, Status.done{k}, d)
    )
  )

# a status that is not refused is not refused
def Status.not_refused(st: Status) -> {Status.is_refused(st) == False{}: Bool} -> {st == Status.refused{}: Status} -> Empty:
  h => d => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Status.is_refused(st),
      True{},
      Equal.sym(Bool, Status.is_refused(st), False{}, h),
      Equal.cong(Status, Bool, x => Status.is_refused(x), st, Status.refused{}, d)
    )
  )

# the status of a verdict is never refused
def Status.verdict_not_refused(m: Maybe<&2, Bool>) -> {Status.is_refused(Status.of.verdict(m)) == False{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

# a held request whose change has the view v is never refused
def Status.view_not_refused(~Q: Data, ~view: Q -> View, s: State(Q), v: View, i: Id) -> {
  Status.is_refused(Status.of.view(~Q, ~view, s, v, i)) == False{}: Bool
}:
  match v:
    case View.root{ms}:
      {==}
    case View.on{c, o, m}:
      Status.verdict_not_refused(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))

# Status.kept once the view v of the request is known
def Status.kept.view(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -k: Bool,
  v: View
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  Status.of.view(~Q, ~view, s, v, i) == Status.done{k}: Status
} -> {Status.of.view(~Q, ~view, State.join(~Q, ~same, s, t), v, i) == Status.done{k}: Status}:
  match v:
    case View.root{ms}:
      ag => h => h
    case View.on{+c, o, m}:
      ag => h =>
        %Equal.sym(
          Maybe<&2, Bool>,
          Steps.verdict(~Q, State.chain(~Q, ~view, State.join(~Q, ~same, s, t), c), i),
          Some{k},
          List.first_prefix(
            ~Step<Q>,
            ~Bool,
            ~Id,
            ~(i => k => Step.verdict(Q, i, k)),
            State.chain(~Q, ~view, s, c),
            State.chain(~Q, ~view, State.join(~Q, ~same, s, t), c),
            i,
            k
          )(
            Equal.trans(
              Maybe<&2, Bool>,
              Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i),
              Status.verdict(Status.of.verdict(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))),
              Some{k},
              Equal.sym(
                Maybe<&2, Bool>,
                Status.verdict(Status.of.verdict(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))),
                Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i),
                Status.verdict_of(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i))
              ),
              Equal.cong(Status, Maybe<&2, Bool>, x => Status.verdict(x), Status.of.verdict(Steps.verdict(~Q, State.chain(~Q, ~view, s, c), i)), Status.done{k}, h)
            )
          )(State.chain_kept(~Q, ~same, ~laws, ~view, s, t, c)(ag))
        ): {Status.of.verdict(_) == Status.done{k}: Status}
        {==}

# Status.kept once the cell m of the request in s is known
def Status.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -k: Bool,
  m: Maybe<&2, Cell<Entry<Q>>>,
  e: {Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)) == m: Maybe<&2, Cell<Entry<Q>>>}
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  Status.of(~Q, ~view, s, i, m) == Status.done{k}: Status
} -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}:
  match m:
    case None{}:
      ag => h => Empty.absurd({State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}, Status.not_done(Status.not_seen{}, k)({==})(h))
    case Some{many{}}:
      ag => h => Empty.absurd({State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}, Status.not_done(Status.refused{}, k)({==})(h))
    case Some{one{Entry.vote{v}}}:
      ag => h => Empty.absurd({State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}, Status.not_done(Status.not_seen{}, k)({==})(h))
    case Some{one{Entry.ask{+j, +tm, +q}}}:
      +ag => h =>
        %Equal.sym(
          Maybe<&2, Cell<Entry<Q>>>,
          Tries.Trie.get(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), Slot.ask(i)),
          Some{one{Entry.ask{j, tm, q}}},
          Cell.agrees_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), s, t, Slot.ask(i), Entry.ask{j, tm, q})(ag)(e)
        ): {Status.of(~Q, ~view, State.join(~Q, ~same, s, t), i, _) == Status.done{k}: Status}
        Status.kept.view(~Q, ~same, ~laws, ~view, s, t, i, k, view(q))(ag)(h)

# a request that a ledger decided stays decided, with the same verdict, in a
# sync that contradicts nothing
law State.status_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  for -k: Bool
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {State.status(~Q, ~view, s, i) == Status.done{k}: Status}
    -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}

def State.status_kept(Q, same, laws, view, s, t, i, k):
  Status.kept.at(~Q, ~same, ~laws, ~view, s, t, i, k, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)), {==})

# a contradicted request stays refused, whatever another cell it meets
def Status.refused_pick(~Q: Data, ~same: Q -> Q -> Bool, ~view: Q -> View, s: State(Q), i: Id, x: Maybe<&2, Cell<Entry<Q>>>) -> {
  Status.of(~Q, ~view, s, i, Tries.Trie.pick(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), Some{many{}}, x)) == Status.refused{}: Status
}:
  match x:
    case None{}:
      {==}
    case Some{y}:
      {==}

# State.refused_kept once the cell m of the request in s is known
def Status.refused.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  m: Maybe<&2, Cell<Entry<Q>>>,
  e: {Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)) == m: Maybe<&2, Cell<Entry<Q>>>}
) -> {
  Status.of(~Q, ~view, s, i, m) == Status.refused{}: Status
} -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}:
  match m:
    case None{}:
      h => Empty.absurd({State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}, Status.not_refused(Status.not_seen{})({==})(h))
    case Some{one{Entry.vote{v}}}:
      h => Empty.absurd({State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}, Status.not_refused(Status.not_seen{})({==})(h))
    case Some{one{Entry.ask{j, tm, +q}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status},
        Status.not_refused(Status.of.view(~Q, ~view, s, view(q), i))(Status.view_not_refused(~Q, ~view, s, view(q), i))(h)
      )
    case Some{many{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cell<Entry<Q>>>,
          Tries.Trie.get(Cell<Entry<Q>>, State.join(~Q, ~same, s, t), Slot.ask(i)),
          Tries.Trie.pick(
            ~Cell<Entry<Q>>,
            ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
            Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)),
            Tries.Trie.get(Cell<Entry<Q>>, t, Slot.ask(i))
          ),
          Tries.Trie.get_union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, t, Slot.ask(i))
        ): {Status.of(~Q, ~view, State.join(~Q, ~same, s, t), i, _) == Status.refused{}: Status}
        %Equal.sym(Maybe<&2, Cell<Entry<Q>>>, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)), Some{many{}}, e):
          {
            Status.of(
              ~Q,
              ~view,
              State.join(~Q, ~same, s, t),
              i,
              Tries.Trie.pick(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), _, Tries.Trie.get(Cell<Entry<Q>>, t, Slot.ask(i)))
            )
              == Status.refused{}: Status
          }
        Status.refused_pick(~Q, ~same, ~view, State.join(~Q, ~same, s, t), i, Tries.Trie.get(Cell<Entry<Q>>, t, Slot.ask(i)))

# a contradicted request stays refused in any sync
law State.refused_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  {State.status(~Q, ~view, s, i) == Status.refused{}: Status}
    -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}

def State.refused_kept(Q, same, view, s, t, i):
  Status.refused.at(~Q, ~same, ~view, s, t, i, Tries.Trie.get(Cell<Entry<Q>>, s, Slot.ask(i)), {==})
