import Base
import ./shared.bend as Shared

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
def Cell.same(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Bool:
  match a b:
    case one{x} one{y}:
      same(x, y)
    case many{} many{}:
      True{}
    case _ _:
      False{}

# Cell.same is True only for equal cells
law Cell.same_sound:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  {Cell.same(~V, ~same, a, b) == True{}: Bool} -> {a == b: Cell<V>}

def Cell.same_sound(ty, same, laws, a, b):
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
  s: Shared.Trie<Cell<V>>,
  t: Shared.Trie<Cell<V>>
) -> Bool:
  match s t:
    case Shared.tip{} y:
      True{}
    case Shared.bin{h, z, o} Shared.tip{}:
      True{}
    case Shared.bin{h1, z1, o1} Shared.bin{h2, z2, o2}:
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
} -> {Shared.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), a, b) == Some{one{v}}: Maybe<&2, Cell<V>>}:
  match a b:
    case None{} y:
      h => g => Empty.absurd(
        {
          Shared.Trie.pick(
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
          Shared.Trie.pick(
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
  for s: Shared.Trie<Cell<V>>
  for t: Shared.Trie<Cell<V>>
  for k: List<&2, Bool>
  for -v: V
  {Cell.agrees(~V, ~same, s, t) == True{}: Bool}
    -> {Shared.Trie.get(Cell<V>, s, k) == Some{one{v}}: Maybe<&2, Cell<V>>}
    -> {
      Shared.Trie.get(
        Cell<V>,
        Shared.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t),
        k
      )
        == Some{one{v}}: Maybe<&2, Cell<V>>
    }

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_kept(ty, same, laws, s, t, k, v):
  match s t k:
    case Shared.tip{} y q:
      a => g => Empty.absurd(
        {Shared.Trie.get(Cell<ty>, y, q) == Some{one{v}}: Maybe<&2, Cell<ty>>},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Cell<ty>>, Bool, m => Cell.is_one(ty, m), None{}, Some{one{v}}, g)
        )
      )
    case Shared.bin{h, z, o} Shared.tip{} q:
      a => g => g
    case Shared.bin{+h1, +z1, +o1} Shared.bin{+h2, +z2, +o2} Nil{}:
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
    case Shared.bin{+h1, +z1, +o1} Shared.bin{+h2, +z2, +o2} Con{False{}, r}:
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
    case Shared.bin{+h1, +z1, +o1} Shared.bin{+h2, +z2, +o2} Con{True{}, r}:
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
  s: Shared.Trie<Cell<V>>
) -> {Cell.agrees(~V, ~same, s, Shared.tip{}) == True{}: Bool}:
  match s:
    case Shared.tip{}:
      {==}
    case Shared.bin{h, z, o}:
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
  for s: Shared.Trie<Cell<V>>
  for k: List<&2, Bool>
  for +x: Cell<V>
  {Shared.Trie.get(Cell<V>, s, k) == None{}: Maybe<&2, Cell<V>>}
    -> {Cell.agrees(~V, ~same, s, Shared.Trie.one(Cell<V>, k, x)) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_one(ty, same, s, k, x):
  match s k:
    case Shared.tip{} q:
      g => {==}
    case Shared.bin{+h, +z, +o} Nil{}:
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
              Cell.agrees(~ty, ~same, z, Shared.tip{}),
              Cell.agrees(~ty, ~same, o, Shared.tip{})
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Cell.agrees(~ty, ~same, z, Shared.tip{}),
          True{},
          Cell.agrees_tip(~ty, ~same, z)
        ):
          {Bool.and(_, Cell.agrees(~ty, ~same, o, Shared.tip{})) == True{}: Bool}
        Cell.agrees_tip(~ty, ~same, o)
    case Shared.bin{+h, +z, +o} Con{False{}, +r}:
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Shared.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Shared.tip{})
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Shared.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Shared.tip{})
        )(Cell.agrees_one(~ty, ~same, z, r, x)(g))(Cell.agrees_tip(~ty, ~same, o))
      )
    case Shared.bin{+h, +z, +o} Con{True{}, +r}:
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Shared.tip{}),
          Cell.agrees(~ty, ~same, o, Shared.Trie.one(Cell<ty>, r, x))
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Shared.tip{}),
          Cell.agrees(~ty, ~same, o, Shared.Trie.one(Cell<ty>, r, x))
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
      +kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
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
      +kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
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

# Replicas
# ========
# A replica holds entries in slots: the requests that writers make, the votes
# of nodes, and the claims of nodes to the first version of a chain. Replicas
# sync by joining what they hold, so every replica that took in the same
# entries holds the same state, in any order and any number of times
# (Shared.Trie.union_comm, union_assoc, union_idem, with the laws of
# Cell.join).
#
# A chain is named by a key. It is a list of versions: its first version is
# the request that a root entry names; each next one is the request that most
# of the chain's owners vote for, after the version before it. A slot with two
# different entries holds many: the request, the vote or the root in it counts
# for nothing.
#
# What a change Q means is the caller's. A replica reads of a change only its
# View, compares changes with same, and asks fits whether the owners of a
# chain may vote for a change at its head.

# Names
# -----

# a request: the writer that made it and the ID that the writer gave it. A
# version is the request that made it.
type Id is Data:
  Id{writer: String, request: String}

# what a replica reads of a change: the key of the chain that it changes, the
# owners that it gives that chain when it sets them, and whether it makes the
# chain when the chain does not exist
type View is Data:
  View{chain: List<&2, Bool>, owners: Maybe<&2, List<&2, String>>, creates: Bool}

# the key of the chain of v
def View.chain(v: View) -> List<&2, Bool>:
  match v:
    case View{c, o, k}:
      c

# the owners after a change of the view v, which ms owned
def View.owners_of(v: View, ms: List<&2, String>) -> List<&2, String>:
  match v:
    case View{c, Some{ns}, k}:
      ns
    case View{c, None{}, k}:
      ms

# a change of the view v makes its chain when the chain does not exist
def View.creates(v: View) -> Bool:
  match v:
    case View{c, o, k}:
      k

# a request of a change, with its time; a vote of a node for a version; or a
# node's claim of the first version of a chain, which that node owns then
type Entry<-Q: Data> is Data:
  Entry.ask{id: Id, time: String, ask: Q}
  Entry.vote{choice: Id}
  Entry.root{chain: List<&2, Bool>, first: Id, owner: String}

# where an entry is: a request by its ID, a vote by its node, its chain and
# the version that it follows, a root by its chain and the node that claims it
type Slot is Data:
  Slot.ask{id: Id}
  Slot.vote{node: String, chain: List<&2, Bool>, after: Id}
  Slot.root{chain: List<&2, Bool>, owner: String}

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Shared.Trie.text(w), Shared.Trie.text(r))

# the start of the keys of the roots of the chain c
def Root.key(c: List<&2, Bool>) -> List<&2, Bool>:
  True{} <> True{} <> c

# the key of k: no two slots share one
def Slot.key(k: Slot) -> List<&2, Bool>:
  match k:
    case Slot.ask{i}:
      False{} <> Id.key(i)
    case Slot.vote{n, c, i}:
      True{}
        <> False{}
        <> List.append(&2, Bool, Shared.Trie.text(n), List.append(&2, Bool, c, Id.key(i)))
    case Slot.root{c, n}:
      List.append(&2, Bool, Root.key(c), Shared.Trie.text(n))

# Entry equality
# --------------

# a and b are the same request
def Id.same(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same key
def Key.same(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  Shared.List.same(~Bool, ~Shared.Bool.same, a, b)

# a and b are the same entry, when same compares changes
def Entry.same(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.ask{i1, t1, q1} Entry.ask{i2, t2, q2}:
      Bool.and(Id.same(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.vote{i1} Entry.vote{i2}:
      Id.same(i1, i2)
    case Entry.root{c1, i1, n1} Entry.root{c2, i2, n2}:
      Bool.and(Key.same(c1, c2), Bool.and(Id.same(i1, i2), String.eq(n1, n2)))
    case _ _:
      False{}

# Id.same is True for a request and itself
def Id.same_refl(a: Id) -> {Id.same(a, a) == True{}: Bool}:
  match a:
    case Id{+w, +r}:
      Shared.Bool.and_both(
        String.eq(w, w),
        String.eq(r, r)
      )(Shared.String.eq_refl(w))(Shared.String.eq_refl(r))

# Id.same is True only for equal requests
def Id.same_sound(a: Id, b: Id) -> {Id.same(a, b) == True{}: Bool} -> {a == b: Id}:
  match a b:
    case Id{+w1, +r1} Id{+w2, +r2}:
      +h =>
        %Shared.String.eq_sound(
          w1,
          w2
        )(Shared.Bool.and_true_left(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Id{w1, r1} == Id{_, r2}: Id}
        %Shared.String.eq_sound(
          r1,
          r2
        )(Shared.Bool.and_true_right(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Id{w1, r1} == Id{w1, _}: Id}
        {==}

# the laws of Id.same
def Id.laws() -> Shared.Eq.Laws(Id, Id.same):
  (Id.same_refl, Id.same_sound)
# Key.same is True for a key and itself
def Key.same_refl(a: List<&2, Bool>) -> {Key.same(a, a) == True{}: Bool}:
  Shared.List.same_refl(~Bool, ~Shared.Bool.same, ~Shared.Bool.laws(), a)

# Key.same is True only for equal keys
def Key.same_sound(
  a: List<&2, Bool>,
  b: List<&2, Bool>
) -> {Key.same(a, b) == True{}: Bool} -> {a == b: List<&2, Bool>}:
  Shared.List.same_sound(~Bool, ~Shared.Bool.same, ~Shared.Bool.laws(), a, b)

# Entry.same is True for an entry and itself
def Entry.same_refl(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>
) -> {Entry.same(~Q, ~same, a, a) == True{}: Bool}:
  match a:
    case Entry.ask{+i, +t, +q}:
      Shared.Bool.and_both(
        Id.same(i, i),
        Bool.and(String.eq(t, t), same(q, q))
      )(
        Id.same_refl(i)
      )(
        Shared.Bool.and_both(
          String.eq(t, t),
          same(q, q)
        )(Shared.String.eq_refl(t))(Shared.Eq.refl(~Q, ~same, laws, q))
      )
    case Entry.vote{i}:
      Id.same_refl(i)
    case Entry.root{+c, +i, +n}:
      Shared.Bool.and_both(
        Key.same(c, c),
        Bool.and(Id.same(i, i), String.eq(n, n))
      )(
        Key.same_refl(c)
      )(
        Shared.Bool.and_both(
          Id.same(i, i),
          String.eq(n, n)
        )(Id.same_refl(i))(Shared.String.eq_refl(n))
      )

# Entry.same is True only for equal entries
def Entry.same_sound(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>,
  b: Entry<Q>
) -> {Entry.same(~Q, ~same, a, b) == True{}: Bool} -> {a == b: Entry<Q>}:
  match a b:
    case Entry.ask{+i1, +t1, +q1} Entry.ask{+i2, +t2, +q2}:
      +h =>
        +r1 = Bool.and(String.eq(t1, t2), same(q1, q2))
        +h1 = Shared.Bool.and_true_right(Id.same(i1, i2), r1)(h)
        %Id.same_sound(i1, i2)(Shared.Bool.and_true_left(Id.same(i1, i2), r1)(h)):
          {Entry.ask{i1, t1, q1} == Entry.ask{_, t2, q2}: Entry<Q>}
        %Shared.String.eq_sound(
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
    case Entry.vote{i1} Entry.vote{i2}:
      h =>
        %Id.same_sound(i1, i2)(h): {Entry.vote{i1} == Entry.vote{_}: Entry<Q>}
        {==}
    case Entry.root{+c1, +i1, +n1} Entry.root{+c2, +i2, +n2}:
      +h =>
        +r1 = Bool.and(Id.same(i1, i2), String.eq(n1, n2))
        +h1 = Shared.Bool.and_true_right(Key.same(c1, c2), r1)(h)
        %Key.same_sound(c1, c2)(Shared.Bool.and_true_left(Key.same(c1, c2), r1)(h)):
          {Entry.root{c1, i1, n1} == Entry.root{_, i2, n2}: Entry<Q>}
        %Id.same_sound(i1, i2)(Shared.Bool.and_true_left(Id.same(i1, i2), String.eq(n1, n2))(h1)):
          {Entry.root{c1, i1, n1} == Entry.root{c1, _, n2}: Entry<Q>}
        %Shared.String.eq_sound(
          n1,
          n2
        )(Shared.Bool.and_true_right(Id.same(i1, i2), String.eq(n1, n2))(h1)):
          {Entry.root{c1, i1, n1} == Entry.root{c1, i1, _}: Entry<Q>}
        {==}
    case Entry.ask{p0, p1, p2} Entry.vote{q0}:
      h => Empty.absurd(
        {Entry.ask{p0, p1, p2} == Entry.vote{q0}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.ask{p0, p1, p2} Entry.root{q0, q1, q2}:
      h => Empty.absurd(
        {Entry.ask{p0, p1, p2} == Entry.root{q0, q1, q2}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.vote{p0} Entry.ask{q0, q1, q2}:
      h => Empty.absurd(
        {Entry.vote{p0} == Entry.ask{q0, q1, q2}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.vote{p0} Entry.root{q0, q1, q2}:
      h => Empty.absurd(
        {Entry.vote{p0} == Entry.root{q0, q1, q2}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.root{p0, p1, p2} Entry.ask{q0, q1, q2}:
      h => Empty.absurd(
        {Entry.root{p0, p1, p2} == Entry.ask{q0, q1, q2}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.root{p0, p1, p2} Entry.vote{q0}:
      h => Empty.absurd(
        {Entry.root{p0, p1, p2} == Entry.vote{q0}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
# the laws of Entry.same, by the laws of same
def Entry.laws(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same)
) -> Shared.Eq.Laws(Entry<Q>, Entry.same(~Q, ~same)):
  (a => Entry.same_refl(~Q, ~same, ~laws, a), a => b => Entry.same_sound(~Q, ~same, ~laws, a, b))

# The state
# ---------

# what a replica of changes Q holds: the cell of each slot, by the slot's key
def State(-Q: Data) -> Data:
  Shared.Trie<Cell<Entry<Q>>>

# a replica that holds nothing yet
def State.empty(~Q: Data) -> State(Q):
  Shared.Trie.new(Cell<Entry<Q>>)

# what a holder of a and of b holds: a sync
def State.join(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q), b: State(Q)) -> State(Q):
  Shared.Trie.union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)), a, b)

# what a holder of r lacks of s: what a sync from s to r sends
# (Shared.Trie.union_minus)
def State.missing(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), r: State(Q)) -> State(Q):
  Shared.Trie.minus(~Cell<Entry<Q>>, ~Cell.same(~Entry<Q>, ~Entry.same(~Q, ~same)), s, r)

# no entry of t contradicts one of s
def State.agrees(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), t: State(Q)) -> Bool:
  Cell.agrees(~Entry<Q>, ~Entry.same(~Q, ~same), s, t)

# the first claim among the cells cs that every holder agrees on
def Root.first(~Q: Data, cs: List<&2, Cell<Entry<Q>>>) -> Maybe<&2, Entry<Q>>:
  match cs:
    case Nil{}:
      None{}
    case Con{one{e}, r}:
      Some{e}
    case Con{many{}, r}:
      Root.first(~Q, r)

# the claim of the first version of the chain c: when nodes claim it apart,
# the one with the smallest key
def State.claim(~Q: Data, s: State(Q), c: List<&2, Bool>) -> Maybe<&2, Entry<Q>>:
  Root.first(
    ~Q,
    Shared.Trie.values(Cell<Entry<Q>>, Shared.Trie.under(Cell<Entry<Q>>, s, Root.key(c)))
  )

# Lookups
# -------

# the entry of a cell, when every holder agrees on it
def Cell.entry(~Q: Data, m: Maybe<&2, Cell<Entry<Q>>>) -> Maybe<&2, Entry<Q>>:
  match m:
    case Some{one{e}}:
      Some{e}
    case _:
      None{}

# the cell of the slot k in s
def State.cell(~Q: Data, s: State(Q), k: Slot) -> Maybe<&2, Cell<Entry<Q>>>:
  Shared.Trie.get(Cell<Entry<Q>>, s, Slot.key(k))

# a request that s holds: its time and change
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
  Asked.of(~Q, Cell.entry(~Q, State.cell(~Q, s, Slot.ask{i})))

# the version that the entry m votes for
def Vote.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Id>:
  match m:
    case Some{Entry.vote{i}}:
      Some{i}
    case _:
      None{}

# where a node votes: in s, on the chain c, after the version v
type Spot<-Q: Data> is Data:
  Spot{state: State(Q), chain: List<&2, Bool>, after: Id}

# the version that the node m votes for at the spot g
def Spot.vote(~Q: Data, g: Spot<Q>, m: String) -> Maybe<&2, Id>:
  match g:
    case Spot{s, c, v}:
      Vote.of(~Q, Cell.entry(~Q, State.cell(~Q, s, Slot.vote{m, c, v})))

# Chains
# ------

# a version of a chain, and the nodes that vote for the next one
type Step is Data:
  Step{version: Id, owners: List<&2, String>}

# the step to i, when its change q is on the chain (held)
def Step.if(
  ~Q: Data,
  ~view: Q -> View,
  held: Bool,
  i: Id,
  q: Q,
  ms: List<&2, String>
) -> Maybe<&2, Step>:
  match held:
    case True{}:
      Some{Step{i, View.owners_of(view(q), ms)}}
    case False{}:
      None{}

# the step to i, when s holds its request r on the chain c
def Step.ask(
  ~Q: Data,
  ~view: Q -> View,
  c: List<&2, Bool>,
  i: Id,
  ms: List<&2, String>,
  r: Maybe<&2, Asked<Q>>
) -> Maybe<&2, Step>:
  match r:
    case None{}:
      None{}
    case Some{Asked{t, +q}}:
      Step.if(~Q, ~view, Key.same(View.chain(view(q)), c), i, q, ms)

# the step to the winner w of a vote, on the chain c of s
def Step.won(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  c: List<&2, Bool>,
  ms: List<&2, String>,
  w: Maybe<&2, Id>
) -> Maybe<&2, Step>:
  match w:
    case None{}:
      None{}
    case Some{+i}:
      Step.ask(~Q, ~view, c, i, ms, State.asked(~Q, s, i))

# the next step of the chain c of s, after the step k
def Chain.next(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: List<&2, Bool>,
  k: Step
) -> Maybe<&2, Step>:
  match k:
    case Step{v, +ms}:
      Step.won(
        ~Q,
        ~view,
        s,
        c,
        ms,
        Quorum.winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, ms, ms, Spot{s, c, v})
      )

# the versions of the chain c of s from the step nx on, f steps at most
def Chain.walk(
  ~Q: Data,
  ~view: Q -> View,
  f: Nat,
  +s: State(Q),
  +c: List<&2, Bool>,
  nx: Maybe<&2, Step>
) -> List<&2, Id>:
  match f nx:
    case 0n m:
      []
    case 1n+e None{}:
      []
    case 1n+e Some{Step{+i, ms}}:
      i <> Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))

# the last step of the chain c of s, from k with the next step nx, f steps at
# most
def Chain.last(
  ~Q: Data,
  ~view: Q -> View,
  f: Nat,
  +s: State(Q),
  +c: List<&2, Bool>,
  k: Step,
  nx: Maybe<&2, Step>
) -> Step:
  match f nx:
    case 0n m:
      k
    case 1n+e None{}:
      k
    case 1n+e Some{+st}:
      Chain.last(~Q, ~view, e, s, c, st, Chain.next(~Q, ~view, s, c, st))

# enough steps for any chain of s: one more than it has entries
def State.fuel(~Q: Data, s: State(Q)) -> Nat:
  1n+Shared.Trie.size(Cell<Entry<Q>>, s)

# the first step of a chain, from its root entry m
def Root.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Step>:
  match m:
    case Some{Entry.root{c, i, n}}:
      Some{Step{i, [n]}}
    case _:
      None{}

# the first step of the chain c, when s holds its root and its request
def Chain.root.of(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  c: List<&2, Bool>,
  m: Maybe<&2, Step>
) -> Maybe<&2, Step>:
  match m:
    case None{}:
      None{}
    case Some{Step{+i, ms}}:
      Step.ask(~Q, ~view, c, i, ms, State.asked(~Q, s, i))

# the first step of the chain c of s
def Chain.root(~Q: Data, ~view: Q -> View, +s: State(Q), +c: List<&2, Bool>) -> Maybe<&2, Step>:
  Chain.root.of(~Q, ~view, s, c, Root.of(~Q, State.claim(~Q, s, c)))

# the versions of the chain c of s, from its first step r
def Chain.from(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: List<&2, Bool>,
  r: Maybe<&2, Step>
) -> List<&2, Id>:
  match r:
    case None{}:
      []
    case Some{Step{+i, ms}}:
      i <> Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))

# the last step of the chain c of s, from its first step r
def Chain.cursor.of(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: List<&2, Bool>,
  r: Maybe<&2, Step>
) -> Maybe<&2, Step>:
  match r:
    case None{}:
      None{}
    case Some{+st}:
      Some{Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st))}

# the last step of the chain c of s, if c exists
def Chain.cursor(~Q: Data, ~view: Q -> View, +s: State(Q), +c: List<&2, Bool>) -> Maybe<&2, Step>:
  Chain.cursor.of(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c))

# the versions of the chain c, in order
def State.chain(~Q: Data, ~view: Q -> View, +s: State(Q), +c: List<&2, Bool>) -> List<&2, Id>:
  Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c))

# the version of a step
def Step.version(k: Step) -> Id:
  match k:
    case Step{v, ms}:
      v

# the owners of a step
def Step.owners(k: Step) -> List<&2, String>:
  match k:
    case Step{v, ms}:
      ms

# the owners at the last step m, none without one
def Step.owners.of(m: Maybe<&2, Step>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{k}:
      Step.owners(k)

# the nodes that vote for the next version of the chain c
def State.owners(~Q: Data, ~view: Q -> View, s: State(Q), c: List<&2, Bool>) -> List<&2, String>:
  Step.owners.of(Chain.cursor(~Q, ~view, s, c))

# the newest version of the chain c, if c exists
def State.head(~Q: Data, ~view: Q -> View, s: State(Q), c: List<&2, Bool>) -> Maybe<&2, Id>:
  Maybe.map(&2, Step, Id, k => Step.version(k), Chain.cursor(~Q, ~view, s, c))

# Changes
# -------

# s with the entry e in the slot k
def State.put(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), k: Slot, e: Entry<Q>) -> State(Q):
  State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, Slot.key(k), one{e}))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the laws of State.ask split on this and; a request is taken in once
# the node n may vote at the step h of the chain c, whose owners are ms
def State.may_vote(
  ~Q: Data,
  +n: String,
  s: State(Q),
  c: List<&2, Bool>,
  h: Id,
  ms: List<&2, String>
) -> Bool:
  Bool.and(
    List.contains(~String, ~String.eq, ms, n),
    Maybe.is_none(&2, Cell<Entry<Q>>, State.cell(~Q, s, Slot.vote{n, c, h}))
  )

# s1 after the node n voted for the request i of q, at the last step m of its
# chain in s
def State.ask.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +n: String,
  +s: State(Q),
  +s1: State(Q),
  i: Id,
  +q: Q,
  m: Maybe<&2, Step>
) -> State(Q):
  match m:
    case None{}:
      s1
    case Some{Step{+h, ms}}:
      +c = View.chain(view(q))
      Bool.pick(
        State(Q),
        Bool.and(State.may_vote(~Q, n, s, c, h, ms), fits(s, q, h)),
        State.put(~Q, ~same, s1, Slot.vote{n, c, h}, Entry.vote{i}),
        s1
      )

# s1 after the node n took in the request i of q, whose chain has the claim m
# in s
def State.ask.root(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +n: String,
  +s: State(Q),
  +s1: State(Q),
  i: Id,
  +q: Q,
  m: Maybe<&2, Entry<Q>>
) -> State(Q):
  match m:
    case None{}:
      Bool.pick(
        State(Q),
        View.creates(view(q)),
        State.put(
          ~Q,
          ~same,
          s1,
          Slot.root{View.chain(view(q)), n},
          Entry.root{View.chain(view(q)), i, n}
        ),
        s1
      )
    case Some{x}:
      State.ask.at(
        ~Q,
        ~same,
        ~view,
        ~fits,
        n,
        s,
        s1,
        i,
        q,
        Chain.cursor(~Q, ~view, s, View.chain(view(q)))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# s after the node n took in the request i of q at the time t, whose cell in s
# is m
def State.ask.fresh(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
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
      State.ask.root(
        ~Q,
        ~same,
        ~view,
        ~fits,
        n,
        s,
        State.put(~Q, ~same, s, Slot.ask{i}, Entry.ask{i, t, q}),
        i,
        q,
        State.claim(~Q, s, View.chain(view(q)))
      )

# s, after the node n took in the request i of q at the time t: the request,
# n's vote for it when n owns its chain and q fits the head, or its root when
# q makes a chain. A request that s holds already changes nothing.
def State.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  q: Q
) -> State(Q):
  State.ask.fresh(~Q, ~same, ~view, ~fits, n, s, i, t, q, State.cell(~Q, s, Slot.ask{i}))

# fits of q at the head h, when the request is not in its chain yet (outside)
def Vote.open.on(
  ~Q: Data,
  ~fits: State(Q) -> Q -> Id -> Bool,
  outside: Bool,
  s: State(Q),
  q: Q,
  h: Id
) -> Bool:
  match outside:
    case True{}:
      fits(s, q, h)
    case False{}:
      False{}

# the request i of q is on the chain (held), is not among its versions xs and
# fits its head h
def Vote.open(
  ~Q: Data,
  ~fits: State(Q) -> Q -> Id -> Bool,
  held: Bool,
  s: State(Q),
  q: Q,
  xs: List<&2, Id>,
  i: Id,
  h: Id
) -> Bool:
  match held:
    case True{}:
      Vote.open.on(~Q, ~fits, Bool.not(List.contains(~Id, ~Id.same, xs, i)), s, q, h)
    case False{}:
      False{}

# the request i, as s holds it in its own slot (m), changes the chain c, is
# not among its versions xs, and fits its head h: the chain reads it there
def Vote.held(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  s: State(Q),
  m: Maybe<&2, Asked<Q>>,
  c: List<&2, Bool>,
  xs: List<&2, Id>,
  i: Id,
  h: Id
) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Asked{t, +q}}:
      Vote.open(~Q, ~fits, Key.same(View.chain(view(q)), c), s, q, xs, i, h)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the first request among the cells cs that s holds in its own slot, changes
# the chain c, is not among its versions xs, and fits its head h
def Vote.pick(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +s: State(Q),
  cs: List<&2, Cell<Entry<Q>>>,
  +c: List<&2, Bool>,
  +xs: List<&2, Id>,
  +h: Id
) -> Maybe<&2, Id>:
  match cs:
    case Nil{}:
      None{}
    case Con{one{Entry.ask{+i, t, q}}, r}:
      Bool.pick(
        Maybe<&2, Id>,
        Vote.held(~Q, ~view, ~fits, s, State.asked(~Q, s, i), c, xs, i, h),
        Some{i},
        Vote.pick(~Q, ~view, ~fits, s, r, c, xs, h)
      )
    case Con{x, r}:
      Vote.pick(~Q, ~view, ~fits, s, r, c, xs, h)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the vote in the slot k for the choice m, when the node may vote (held)
def Vote.cast(~Q: Data, held: Bool, k: Slot, m: Maybe<&2, Id>) -> State(Q):
  match held m:
    case True{} Some{i}:
      Shared.Trie.one(Cell<Entry<Q>>, Slot.key(k), one{Entry.vote{i}})
    case h w:
      Shared.tip{}

# the vote of the node n on the chain c of s, at its last step m
def Vote.at(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +n: String,
  +s: State(Q),
  +c: List<&2, Bool>,
  m: Maybe<&2, Step>
) -> State(Q):
  match m:
    case None{}:
      Shared.tip{}
    case Some{Step{+h, ms}}:
      Vote.cast(
        ~Q,
        State.may_vote(~Q, n, s, c, h, ms),
        Slot.vote{n, c, h},
        Vote.pick(
          ~Q,
          ~view,
          ~fits,
          s,
          Shared.Trie.values(Cell<Entry<Q>>, s),
          c,
          State.chain(~Q, ~view, s, c),
          h
        )
      )

# the chains whose roots are among the cells cs
def Vote.chains(~Q: Data, cs: List<&2, Cell<Entry<Q>>>) -> List<&2, List<&2, Bool>>:
  match cs:
    case Nil{}:
      []
    case Con{one{Entry.root{+c, i, n}}, r}:
      +rest = Vote.chains(~Q, r)
      List.filter.put(
        List<&2, Bool>,
        c,
        rest,
        Bool.not(List.contains(~List<&2, Bool>, ~Key.same, rest, c))
      )
    case Con{x, r}:
      Vote.chains(~Q, r)

# the votes of the node n on each chain of cs
def Vote.all(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +n: String,
  +s: State(Q),
  cs: List<&2, List<&2, Bool>>
) -> State(Q):
  match cs:
    case Nil{}:
      Shared.tip{}
    case Con{+c, r}:
      State.join(
        ~Q,
        ~same,
        Vote.at(~Q, ~view, ~fits, n, s, c, Chain.cursor(~Q, ~view, s, c)),
        Vote.all(~Q, ~same, ~view, ~fits, n, s, r)
      )

# s, after the node n voted at the head of each chain that it owns, for the
# first request there that fits it
def State.vote(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  n: String,
  +s: State(Q)
) -> State(Q):
  State.join(
    ~Q,
    ~same,
    s,
    Vote.all(~Q, ~same, ~view, ~fits, n, s, Vote.chains(~Q, Shared.Trie.values(Cell<Entry<Q>>, s)))
  )

# Status
# ------

# where a request is. Done: in its chain, with what that gives (State.status
# gives its change). Pending: not in its chain yet, and its owners may still
# vote for it. Stale: its owners cannot vote for it at the head any more.
# Refused: it, or its chain, is contradicted, or it changes a chain that does
# not exist.
type Status<-D: Data> is Data:
  Status.done{result: D}
  Status.pending{}
  Status.stale{head: Id}
  Status.refused{why: String}
  Status.not_seen{}

# the status of a request of q outside its chain, whose claim is m and last
# step k
def Status.open(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  s: State(Q),
  q: Q,
  m: Maybe<&2, Entry<Q>>,
  k: Maybe<&2, Step>
) -> Status<Q>:
  match m k:
    case w Some{Step{+h, ms}}:
      Bool.pick(Status<Q>, fits(s, q, h), Status.pending{}, Status.stale{h})
    case None{} None{}:
      Bool.pick(Status<Q>, View.creates(view(q)), Status.pending{}, Status.refused{"no such chain"})
    case Some{e} None{}:
      Status.pending{}

# the status of a request of q, in its chain or not (held)
def Status.in(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +s: State(Q),
  +q: Q,
  held: Bool
) -> Status<Q>:
  match held:
    case True{}:
      Status.done{q}
    case False{}:
      Status.open(
        ~Q,
        ~view,
        ~fits,
        s,
        q,
        State.claim(~Q, s, View.chain(view(q))),
        Chain.cursor(~Q, ~view, s, View.chain(view(q)))
      )

# the status of the request i, whose cell is m
def Status.of(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +s: State(Q),
  i: Id,
  m: Maybe<&2, Cell<Entry<Q>>>
) -> Status<Q>:
  match m:
    case None{}:
      Status.not_seen{}
    case Some{many{}}:
      Status.refused{"the request is contradicted"}
    case Some{one{Entry.ask{j, t, +q}}}:
      Status.in(
        ~Q,
        ~view,
        ~fits,
        s,
        q,
        List.contains(~Id, ~Id.same, State.chain(~Q, ~view, s, View.chain(view(q))), i)
      )
    case Some{one{e}}:
      Status.not_seen{}

# where the request i is
def State.status(
  ~Q: Data,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  +s: State(Q),
  +i: Id
) -> Status<Q>:
  Status.of(~Q, ~view, ~fits, s, i, State.cell(~Q, s, Slot.ask{i}))

# Kept entries
# ------------
# What a node holds stays when it takes in entries that agree with it.

# the cell of a slot is kept by an agreeing join
def Kept.cell(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  t: State(Q),
  k: Slot,
  -e: Entry<Q>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  State.cell(~Q, s, k) == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>
} -> {State.cell(~Q, State.join(~Q, ~same, s, t), k) == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>}:
  Cell.agrees_kept(
    ~Entry<Q>,
    ~Entry.same(~Q, ~same),
    ~Entry.laws(~Q, ~same, ~laws),
    s,
    t,
    Slot.key(k),
    e
  )(a)

# the entry of a cell m is kept in m2, when m2 keeps the value of m
def Kept.entry(
  ~Q: Data,
  m: Maybe<&2, Cell<Entry<Q>>>,
  m2: Maybe<&2, Cell<Entry<Q>>>,
  -e: Entry<Q>,
  keep: {
    m == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>
  } -> {m2 == Some{one{e}}: Maybe<&2, Cell<Entry<Q>>>}
) -> {
  Cell.entry(~Q, m) == Some{e}: Maybe<&2, Entry<Q>>
} -> {Cell.entry(~Q, m2) == Some{e}: Maybe<&2, Entry<Q>>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {Cell.entry(~Q, m2) == Some{e}: Maybe<&2, Entry<Q>>},
        Shared.Maybe.none_ne_some(Entry<Q>, e, h)
      )
    case Some{many{}}:
      h => Empty.absurd(
        {Cell.entry(~Q, m2) == Some{e}: Maybe<&2, Entry<Q>>},
        Shared.Maybe.none_ne_some(Entry<Q>, e, h)
      )
    case Some{one{x}}:
      h =>
        +xe = Shared.Maybe.some_inj(Entry<Q>, x, e, h)
        %Equal.sym(
          Maybe<&2, Cell<Entry<Q>>>,
          m2,
          Some{one{e}},
          keep(%xe: {Some{one{x}} == Some{one{_}}: Maybe<&2, Cell<Entry<Q>>>}; {==})
        ):
          {Cell.entry(~Q, _) == Some{e}: Maybe<&2, Entry<Q>>}
        {==}

# the entry of the slot k is kept by an agreeing join
def Kept.slot(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +k: Slot,
  -e: Entry<Q>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Cell.entry(~Q, State.cell(~Q, s, k)) == Some{e}: Maybe<&2, Entry<Q>>
} -> {
  Cell.entry(~Q, State.cell(~Q, State.join(~Q, ~same, s, t), k)) == Some{e}: Maybe<&2, Entry<Q>>
}:
  Kept.entry(
    ~Q,
    State.cell(~Q, s, k),
    State.cell(~Q, State.join(~Q, ~same, s, t), k),
    e,
    Kept.cell(~Q, ~same, ~laws, s, t, k, e, a)
  )

# a request that x names is named by y, when y keeps the entry of x
def Kept.asked.of(
  ~Q: Data,
  x: Maybe<&2, Entry<Q>>,
  y: Maybe<&2, Entry<Q>>,
  -r: Asked<Q>,
  keep: @e: Entry<Q> -> {x == Some{e}: Maybe<&2, Entry<Q>>} -> {y == Some{e}: Maybe<&2, Entry<Q>>}
) -> {
  Asked.of(~Q, x) == Some{r}: Maybe<&2, Asked<Q>>
} -> {Asked.of(~Q, y) == Some{r}: Maybe<&2, Asked<Q>>}:
  match x:
    case None{}:
      h => Empty.absurd(
        {Asked.of(~Q, y) == Some{r}: Maybe<&2, Asked<Q>>},
        Shared.Maybe.none_ne_some(Asked<Q>, r, h)
      )
    case Some{e}:
      h =>
        %Equal.sym(
          Maybe<&2, Entry<Q>>,
          y,
          Some{e},
          keep(e)({==})
        ): {Asked.of(~Q, _) == Some{r}: Maybe<&2, Asked<Q>>}
        h

# a request that s holds is kept by an agreeing join
def Kept.asked(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -r: Asked<Q>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  State.asked(~Q, s, i) == Some{r}: Maybe<&2, Asked<Q>>
} -> {State.asked(~Q, State.join(~Q, ~same, s, t), i) == Some{r}: Maybe<&2, Asked<Q>>}:
  Kept.asked.of(
    ~Q,
    Cell.entry(~Q, State.cell(~Q, s, Slot.ask{i})),
    Cell.entry(~Q, State.cell(~Q, State.join(~Q, ~same, s, t), Slot.ask{i})),
    r,
    e => Kept.slot(~Q, ~same, ~laws, s, t, Slot.ask{i}, e, a)
  )

# a vote that x holds is held by y, when y keeps the entry of x
def Kept.vote.of(
  ~Q: Data,
  x: Maybe<&2, Entry<Q>>,
  y: Maybe<&2, Entry<Q>>,
  -j: Id,
  keep: @e: Entry<Q> -> {x == Some{e}: Maybe<&2, Entry<Q>>} -> {y == Some{e}: Maybe<&2, Entry<Q>>}
) -> {Vote.of(~Q, x) == Some{j}: Maybe<&2, Id>} -> {Vote.of(~Q, y) == Some{j}: Maybe<&2, Id>}:
  match x:
    case None{}:
      h => Empty.absurd(
        {Vote.of(~Q, y) == Some{j}: Maybe<&2, Id>},
        Shared.Maybe.none_ne_some(Id, j, h)
      )
    case Some{e}:
      h =>
        %Equal.sym(
          Maybe<&2, Entry<Q>>,
          y,
          Some{e},
          keep(e)({==})
        ): {Vote.of(~Q, _) == Some{j}: Maybe<&2, Id>}
        h

# a vote kept as y is a vote that the quorum keeps
def Kept.one.at(
  x: Maybe<&2, Id>,
  y: Maybe<&2, Id>,
  keep: @j: Id -> {x == Some{j}: Maybe<&2, Id>} -> {y == Some{j}: Maybe<&2, Id>}
) -> {Quorum.kept(~Id, ~Id.same, x, y) == True{}: Bool}:
  match x:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Maybe<&2, Id>, y, Some{j}, keep(j)({==})):
        {Quorum.hit(~Id, ~Id.same, _, j) == True{}: Bool}
      Id.same_refl(j)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# every vote at the spot of s is kept by an agreeing join
def Kept.keeps(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +v: Id,
  ms: List<&2, String>,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Quorum.keeps(
    ~String,
    ~Id,
    ~Spot<Q>,
    ~Spot.vote(~Q),
    ~Id.same,
    ms,
    Spot{s, c, v},
    Spot{State.join(~Q, ~same, s, t), c, v}
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      Shared.Bool.and_both(
        Quorum.kept(
          ~Id,
          ~Id.same,
          Spot.vote(~Q, Spot{s, c, v}, m),
          Spot.vote(~Q, Spot{State.join(~Q, ~same, s, t), c, v}, m)
        ),
        Quorum.keeps(
          ~String,
          ~Id,
          ~Spot<Q>,
          ~Spot.vote(~Q),
          ~Id.same,
          r,
          Spot{s, c, v},
          Spot{State.join(~Q, ~same, s, t), c, v}
        )
      )(
        Kept.one.at(
          Spot.vote(~Q, Spot{s, c, v}, m),
          Spot.vote(~Q, Spot{State.join(~Q, ~same, s, t), c, v}, m),
          j => Kept.vote.of(
            ~Q,
            Cell.entry(~Q, State.cell(~Q, s, Slot.vote{m, c, v})),
            Cell.entry(~Q, State.cell(~Q, State.join(~Q, ~same, s, t), Slot.vote{m, c, v})),
            j,
            e => Kept.slot(~Q, ~same, ~laws, s, t, Slot.vote{m, c, v}, e, a)
          )
        )
      )(Kept.keeps(~Q, ~same, ~laws, s, t, c, v, r, a))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a step to i that s holds the request of is kept by an agreeing join
def Kept.step.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  s: State(Q),
  t: State(Q),
  c: List<&2, Bool>,
  i: Id,
  ms: List<&2, String>,
  -st: Step,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  r: Maybe<&2, Asked<Q>>,
  er: {State.asked(~Q, s, i) == r: Maybe<&2, Asked<Q>>}
) -> {
  Step.ask(~Q, ~view, c, i, ms, r) == Some{st}: Maybe<&2, Step>
} -> {
  Step.ask(
    ~Q,
    ~view,
    c,
    i,
    ms,
    State.asked(~Q, State.join(~Q, ~same, s, t), i)
  )
    == Some{st}: Maybe<&2, Step>
}:
  match r:
    case None{}:
      h => Empty.absurd(
        {
          Step.ask(
            ~Q,
            ~view,
            c,
            i,
            ms,
            State.asked(~Q, State.join(~Q, ~same, s, t), i)
          )
            == Some{st}: Maybe<&2, Step>
        },
        Shared.Maybe.none_ne_some(Step, st, h)
      )
    case Some{x}:
      h =>
        %Equal.sym(
          Maybe<&2, Asked<Q>>,
          State.asked(~Q, State.join(~Q, ~same, s, t), i),
          Some{x},
          Kept.asked(~Q, ~same, ~laws, s, t, i, x, a)(er)
        ):
          {Step.ask(~Q, ~view, c, i, ms, _) == Some{st}: Maybe<&2, Step>}
        h
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Kept.next once the winner w of the vote in s is known
def Kept.next.won(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +v: Id,
  +ms: List<&2, String>,
  -st: Step,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  w: Maybe<&2, Id>,
  ew: {
    Quorum.winner(
      ~String,
      ~Id,
      ~Spot<Q>,
      ~Spot.vote(~Q),
      ~Id.same,
      ms,
      ms,
      Spot{s, c, v}
    )
      == w: Maybe<&2, Id>
  }
) -> {
  Step.won(~Q, ~view, s, c, ms, w) == Some{st}: Maybe<&2, Step>
} -> {
  Step.won(
    ~Q,
    ~view,
    State.join(~Q, ~same, s, t),
    c,
    ms,
    Quorum.winner(
      ~String,
      ~Id,
      ~Spot<Q>,
      ~Spot.vote(~Q),
      ~Id.same,
      ms,
      ms,
      Spot{State.join(~Q, ~same, s, t), c, v}
    )
  )
    == Some{st}: Maybe<&2, Step>
}:
  match w:
    case None{}:
      h => Empty.absurd(
        {
          Step.won(
            ~Q,
            ~view,
            State.join(~Q, ~same, s, t),
            c,
            ms,
            Quorum.winner(
              ~String,
              ~Id,
              ~Spot<Q>,
              ~Spot.vote(~Q),
              ~Id.same,
              ms,
              ms,
              Spot{State.join(~Q, ~same, s, t), c, v}
            )
          )
            == Some{st}: Maybe<&2, Step>
        },
        Shared.Maybe.none_ne_some(Step, st, h)
      )
    case Some{+i}:
      h =>
        +g = {Spot{s, c, v}: Spot<Q>}
        +g2 = {Spot{State.join(~Q, ~same, s, t), c, v}: Spot<Q>}
        +won = Quorum.winner_of(
          ~String,
          ~Id,
          ~Spot<Q>,
          ~Spot.vote(~Q),
          ~Id.same,
          ~Id.laws(),
          ms,
          g2,
          i
        )(
          Quorum.has_more(
            ~String,
            ~Id,
            ~Spot<Q>,
            ~Spot.vote(~Q),
            ~Id.same,
            ~Id.laws(),
            ms,
            g,
            g2,
            i
          )(
            Kept.keeps(~Q, ~same, ~laws, s, t, c, v, ms, a)
          )(Quorum.has_winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, ms, ms, g, i)(ew))
        )
        %Equal.sym(
          Maybe<&2, Id>,
          Quorum.winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, ms, ms, g2),
          Some{i},
          won
        ):
          {Step.won(~Q, ~view, State.join(~Q, ~same, s, t), c, ms, _) == Some{st}: Maybe<&2, Step>}
        Kept.step.ask(
          ~Q,
          ~same,
          ~laws,
          ~view,
          s,
          t,
          c,
          i,
          ms,
          st,
          a,
          State.asked(~Q, s, i),
          {==}
        )(h)

# a next step of s is kept by an agreeing join
def Kept.next(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  +c: List<&2, Bool>,
  k: Step,
  -st: Step,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Chain.next(~Q, ~view, s, c, k) == Some{st}: Maybe<&2, Step>
} -> {Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k) == Some{st}: Maybe<&2, Step>}:
  match k:
    case Step{+v, +ms}:
      Kept.next.won(
        ~Q,
        ~same,
        ~laws,
        ~view,
        s,
        t,
        c,
        v,
        ms,
        st,
        a,
        Quorum.winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, ms, ms, Spot{s, c, v}),
        {==}
      )

# Walks
# -----

# a walk from no next step is empty
def Walk.none(
  ~Q: Data,
  ~view: Q -> View,
  +g: Nat,
  s: State(Q),
  c: List<&2, Bool>
) -> {Chain.walk(~Q, ~view, g, s, c, None{}) == []: List<&2, Id>}:
  match g:
    case 0n:
      {==}
    case 1n+e:
      {==}

# a walk from no next step ends where it starts
def Last.none(
  ~Q: Data,
  ~view: Q -> View,
  +g: Nat,
  s: State(Q),
  c: List<&2, Bool>,
  k: Step
) -> {Chain.last(~Q, ~view, g, s, c, k, None{}) == k: Step}:
  match g:
    case 0n:
      {==}
    case 1n+e:
      {==}

# a walk of f steps has at most f versions
def Walk.length(
  ~Q: Data,
  ~view: Q -> View,
  +f: Nat,
  +s: State(Q),
  +c: List<&2, Bool>,
  nx: Maybe<&2, Step>
) -> {Nat.is_le(List.length(&2, Id, Chain.walk(~Q, ~view, f, s, c, nx)), f) == True{}: Bool}:
  match f nx:
    case 0n m:
      {==}
    case 1n+e None{}:
      {==}
    case 1n+e Some{Step{i, ms}}:
      Walk.length(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Ext.walk once the next step nx after k in s is known
def Ext.walk.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  e: Nat,
  g: Nat,
  s: State(Q),
  t: State(Q),
  c: List<&2, Bool>,
  k: Step,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  nx: Maybe<&2, Step>,
  enx: {Chain.next(~Q, ~view, s, c, k) == nx: Maybe<&2, Step>},
  ih: @k2: Step -> {
    Nat.is_le(e, g) == True{}: Bool
  } -> {
    Chain.walk(
      ~Q,
      ~view,
      g,
      State.join(~Q, ~same, s, t),
      c,
      Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k2)
    )
      == List.append(
        &2,
        Id,
        Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, k2)),
        Chain.walk(
          ~Q,
          ~view,
          Nat.sub(
            g,
            List.length(&2, Id, Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, k2)))
          ),
          State.join(~Q, ~same, s, t),
          c,
          Chain.next(
            ~Q,
            ~view,
            State.join(~Q, ~same, s, t),
            c,
            Chain.last(~Q, ~view, e, s, c, k2, Chain.next(~Q, ~view, s, c, k2))
          )
        )
      ): List<&2, Id>
  }
) -> {
  Nat.is_le(e, g) == True{}: Bool
} -> {
  Chain.walk(
    ~Q,
    ~view,
    1n+g,
    State.join(~Q, ~same, s, t),
    c,
    Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
  )
    == List.append(
      &2,
      Id,
      Chain.walk(~Q, ~view, 1n+e, s, c, nx),
      Chain.walk(
        ~Q,
        ~view,
        Nat.sub(1n+g, List.length(&2, Id, Chain.walk(~Q, ~view, 1n+e, s, c, nx))),
        State.join(~Q, ~same, s, t),
        c,
        Chain.next(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Chain.last(~Q, ~view, 1n+e, s, c, k, nx)
        )
      )
    ): List<&2, Id>
}:
  match nx:
    case None{}:
      le =>
        %Equal.sym(Nat, Nat.sub(1n+g, 0n), 1n+g, Shared.Nat.sub_zero(1n+g)):
          {
            Chain.walk(
              ~Q,
              ~view,
              1n+g,
              State.join(~Q, ~same, s, t),
              c,
              Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
            )
              == Chain.walk(
                ~Q,
                ~view,
                _,
                State.join(~Q, ~same, s, t),
                c,
                Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
              ): List<&2, Id>
          }
        {==}
    case Some{Step{i, ms}}:
      le =>
        %Equal.sym(
          Maybe<&2, Step>,
          Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k),
          Some{Step{i, ms}},
          Kept.next(~Q, ~same, ~laws, ~view, s, t, c, k, Step{i, ms}, a)(enx)
        ):
          {
            Chain.walk(
              ~Q,
              ~view,
              1n+g,
              State.join(~Q, ~same, s, t),
              c,
              _
            )
              == List.append(
                &2,
                Id,
                i <> Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, Step{i, ms})),
                Chain.walk(
                  ~Q,
                  ~view,
                  Nat.sub(
                    1n+g,
                    1n+List.length(
                      &2,
                      Id,
                      Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))
                    )
                  ),
                  State.join(~Q, ~same, s, t),
                  c,
                  Chain.next(
                    ~Q,
                    ~view,
                    State.join(~Q, ~same, s, t),
                    c,
                    Chain.last(
                      ~Q,
                      ~view,
                      e,
                      s,
                      c,
                      Step{i, ms},
                      Chain.next(~Q, ~view, s, c, Step{i, ms})
                    )
                  )
                )
              ): List<&2, Id>
          }
        %ih(Step{i, ms})(le):
          {
            i
              <> Chain.walk(
                ~Q,
                ~view,
                g,
                State.join(~Q, ~same, s, t),
                c,
                Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, Step{i, ms})
              )
              == i
              <> _: List<&2, Id>
          }
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a walk of s, then the walk of s and t from where it ended, is the walk of s
# and t: when t agrees with s, and s and t walk at least as far
def Ext.walk(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +f: Nat,
  +g: Nat,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +k: Step,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Nat.is_le(f, g) == True{}: Bool
} -> {
  Chain.walk(
    ~Q,
    ~view,
    g,
    State.join(~Q, ~same, s, t),
    c,
    Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
  )
    == List.append(
      &2,
      Id,
      Chain.walk(~Q, ~view, f, s, c, Chain.next(~Q, ~view, s, c, k)),
      Chain.walk(
        ~Q,
        ~view,
        Nat.sub(
          g,
          List.length(&2, Id, Chain.walk(~Q, ~view, f, s, c, Chain.next(~Q, ~view, s, c, k)))
        ),
        State.join(~Q, ~same, s, t),
        c,
        Chain.next(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Chain.last(~Q, ~view, f, s, c, k, Chain.next(~Q, ~view, s, c, k))
        )
      )
    ): List<&2, Id>
}:
  match f g:
    case 0n w:
      le =>
        %Equal.sym(Nat, Nat.sub(w, 0n), w, Shared.Nat.sub_zero(w)):
          {
            Chain.walk(
              ~Q,
              ~view,
              w,
              State.join(~Q, ~same, s, t),
              c,
              Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
            )
              == Chain.walk(
                ~Q,
                ~view,
                _,
                State.join(~Q, ~same, s, t),
                c,
                Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
              ): List<&2, Id>
          }
        {==}
    case 1n+e 0n:
      le => Empty.absurd(
        {
          Chain.walk(
            ~Q,
            ~view,
            0n,
            State.join(~Q, ~same, s, t),
            c,
            Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
          )
            == List.append(
              &2,
              Id,
              Chain.walk(~Q, ~view, 1n+e, s, c, Chain.next(~Q, ~view, s, c, k)),
              Chain.walk(
                ~Q,
                ~view,
                Nat.sub(
                  0n,
                  List.length(
                    &2,
                    Id,
                    Chain.walk(~Q, ~view, 1n+e, s, c, Chain.next(~Q, ~view, s, c, k))
                  )
                ),
                State.join(~Q, ~same, s, t),
                c,
                Chain.next(
                  ~Q,
                  ~view,
                  State.join(~Q, ~same, s, t),
                  c,
                  Chain.last(~Q, ~view, 1n+e, s, c, k, Chain.next(~Q, ~view, s, c, k))
                )
              )
            ): List<&2, Id>
        },
        Shared.Bool.false_ne_true(le)
      )
    case 1n+e 1n+h:
      Ext.walk.at(
        ~Q,
        ~same,
        ~laws,
        ~view,
        e,
        h,
        s,
        t,
        c,
        k,
        a,
        Chain.next(~Q, ~view, s, c, k),
        {==},
        k2 => Ext.walk(~Q, ~same, ~laws, ~view, e, h, s, t, c, k2, a)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Ext.last once the next step nx after k in s is known
def Ext.last.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  e: Nat,
  g: Nat,
  s: State(Q),
  t: State(Q),
  c: List<&2, Bool>,
  k: Step,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  nx: Maybe<&2, Step>,
  enx: {Chain.next(~Q, ~view, s, c, k) == nx: Maybe<&2, Step>},
  ih: @k2: Step -> {
    Nat.is_le(e, g) == True{}: Bool
  } -> {
    Chain.last(
      ~Q,
      ~view,
      g,
      State.join(~Q, ~same, s, t),
      c,
      k2,
      Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k2)
    )
      == Chain.last(
        ~Q,
        ~view,
        Nat.sub(
          g,
          List.length(&2, Id, Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, k2)))
        ),
        State.join(~Q, ~same, s, t),
        c,
        Chain.last(~Q, ~view, e, s, c, k2, Chain.next(~Q, ~view, s, c, k2)),
        Chain.next(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Chain.last(~Q, ~view, e, s, c, k2, Chain.next(~Q, ~view, s, c, k2))
        )
      ): Step
  }
) -> {
  Nat.is_le(e, g) == True{}: Bool
} -> {
  Chain.last(
    ~Q,
    ~view,
    1n+g,
    State.join(~Q, ~same, s, t),
    c,
    k,
    Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
  )
    == Chain.last(
      ~Q,
      ~view,
      Nat.sub(1n+g, List.length(&2, Id, Chain.walk(~Q, ~view, 1n+e, s, c, nx))),
      State.join(~Q, ~same, s, t),
      c,
      Chain.last(~Q, ~view, 1n+e, s, c, k, nx),
      Chain.next(
        ~Q,
        ~view,
        State.join(~Q, ~same, s, t),
        c,
        Chain.last(~Q, ~view, 1n+e, s, c, k, nx)
      )
    ): Step
}:
  match nx:
    case None{}:
      le => {==}
    case Some{Step{i, ms}}:
      le =>
        %Equal.sym(
          Maybe<&2, Step>,
          Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k),
          Some{Step{i, ms}},
          Kept.next(~Q, ~same, ~laws, ~view, s, t, c, k, Step{i, ms}, a)(enx)
        ):
          {
            Chain.last(
              ~Q,
              ~view,
              1n+g,
              State.join(~Q, ~same, s, t),
              c,
              k,
              _
            )
              == Chain.last(
                ~Q,
                ~view,
                Nat.sub(
                  g,
                  List.length(
                    &2,
                    Id,
                    Chain.walk(~Q, ~view, e, s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))
                  )
                ),
                State.join(~Q, ~same, s, t),
                c,
                Chain.last(
                  ~Q,
                  ~view,
                  e,
                  s,
                  c,
                  Step{i, ms},
                  Chain.next(~Q, ~view, s, c, Step{i, ms})
                ),
                Chain.next(
                  ~Q,
                  ~view,
                  State.join(~Q, ~same, s, t),
                  c,
                  Chain.last(
                    ~Q,
                    ~view,
                    e,
                    s,
                    c,
                    Step{i, ms},
                    Chain.next(~Q, ~view, s, c, Step{i, ms})
                  )
                )
              ): Step
          }
        ih(Step{i, ms})(le)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the last step of s, walked on in s and t, is the last step of s and t: when t
# agrees with s, and s and t walk at least as far
def Ext.last(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +f: Nat,
  +g: Nat,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +k: Step,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Nat.is_le(f, g) == True{}: Bool
} -> {
  Chain.last(
    ~Q,
    ~view,
    g,
    State.join(~Q, ~same, s, t),
    c,
    k,
    Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
  )
    == Chain.last(
      ~Q,
      ~view,
      Nat.sub(
        g,
        List.length(&2, Id, Chain.walk(~Q, ~view, f, s, c, Chain.next(~Q, ~view, s, c, k)))
      ),
      State.join(~Q, ~same, s, t),
      c,
      Chain.last(~Q, ~view, f, s, c, k, Chain.next(~Q, ~view, s, c, k)),
      Chain.next(
        ~Q,
        ~view,
        State.join(~Q, ~same, s, t),
        c,
        Chain.last(~Q, ~view, f, s, c, k, Chain.next(~Q, ~view, s, c, k))
      )
    ): Step
}:
  match f g:
    case 0n w:
      le =>
        %Equal.sym(Nat, Nat.sub(w, 0n), w, Shared.Nat.sub_zero(w)):
          {
            Chain.last(
              ~Q,
              ~view,
              w,
              State.join(~Q, ~same, s, t),
              c,
              k,
              Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
            )
              == Chain.last(
                ~Q,
                ~view,
                _,
                State.join(~Q, ~same, s, t),
                c,
                k,
                Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
              ): Step
          }
        {==}
    case 1n+e 0n:
      le => Empty.absurd(
        {
          Chain.last(
            ~Q,
            ~view,
            0n,
            State.join(~Q, ~same, s, t),
            c,
            k,
            Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, k)
          )
            == Chain.last(
              ~Q,
              ~view,
              Nat.sub(
                0n,
                List.length(
                  &2,
                  Id,
                  Chain.walk(~Q, ~view, 1n+e, s, c, Chain.next(~Q, ~view, s, c, k))
                )
              ),
              State.join(~Q, ~same, s, t),
              c,
              Chain.last(~Q, ~view, 1n+e, s, c, k, Chain.next(~Q, ~view, s, c, k)),
              Chain.next(
                ~Q,
                ~view,
                State.join(~Q, ~same, s, t),
                c,
                Chain.last(~Q, ~view, 1n+e, s, c, k, Chain.next(~Q, ~view, s, c, k))
              )
            ): Step
        },
        Shared.Bool.false_ne_true(le)
      )
    case 1n+e 1n+h:
      Ext.last.at(
        ~Q,
        ~same,
        ~laws,
        ~view,
        e,
        h,
        s,
        t,
        c,
        k,
        a,
        Chain.next(~Q, ~view, s, c, k),
        {==},
        k2 => Ext.last(~Q, ~same, ~laws, ~view, e, h, s, t, c, k2, a)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Chains kept
# -----------

# an agreeing join walks at least as far
def State.fuel_le(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  t: State(Q)
) -> {Nat.is_le(State.fuel(~Q, s), State.fuel(~Q, State.join(~Q, ~same, s, t))) == True{}: Bool}:
  Shared.Trie.size_union(~Cell<Entry<Q>>, ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)), s, t)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# State.chain_kept from the first step m
def Kept.chain.from(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  m: Maybe<&2, Step>
) -> {
  List.take(
    &2,
    Id,
    Chain.from(~Q, ~view, State.join(~Q, ~same, s, t), c, m),
    List.length(&2, Id, Chain.from(~Q, ~view, s, c, m))
  )
    == Chain.from(~Q, ~view, s, c, m): List<&2, Id>
}:
  match m:
    case None{}:
      {==}
    case Some{Step{+i, +ms}}:
      +w = Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))
      x = Chain.walk(
        ~Q,
        ~view,
        Nat.sub(State.fuel(~Q, State.join(~Q, ~same, s, t)), List.length(&2, Id, w)),
        State.join(~Q, ~same, s, t),
        c,
        Chain.next(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Chain.last(
            ~Q,
            ~view,
            State.fuel(~Q, s),
            s,
            c,
            Step{i, ms},
            Chain.next(~Q, ~view, s, c, Step{i, ms})
          )
        )
      )
      %Equal.sym(
        List<&2, Id>,
        Chain.walk(
          ~Q,
          ~view,
          State.fuel(~Q, State.join(~Q, ~same, s, t)),
          State.join(~Q, ~same, s, t),
          c,
          Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, Step{i, ms})
        ),
        List.append(&2, Id, w, x),
        Ext.walk(
          ~Q,
          ~same,
          ~laws,
          ~view,
          State.fuel(~Q, s),
          State.fuel(~Q, State.join(~Q, ~same, s, t)),
          s,
          t,
          c,
          Step{i, ms},
          a
        )(State.fuel_le(~Q, ~same, s, t))
      ):
        {List.take(&2, Id, i <> _, 1n+List.length(&2, Id, w)) == i <> w: List<&2, Id>}
      %Shared.List.take_append(
        Id,
        w,
        x
      ): {
        i
          <> List.take(&2, Id, List.append(&2, Id, w, x), List.length(&2, Id, w))
          == i
          <> _: List<&2, Id>
      }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# State.chain_kept once the request r of the first version i is known
def Kept.chain.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +i: Id,
  ms: List<&2, String>,
  r: Maybe<&2, Asked<Q>>,
  er: {State.asked(~Q, s, i) == r: Maybe<&2, Asked<Q>>}
) -> {
  List.take(
    &2,
    Id,
    Chain.from(
      ~Q,
      ~view,
      State.join(~Q, ~same, s, t),
      c,
      Step.ask(~Q, ~view, c, i, ms, State.asked(~Q, State.join(~Q, ~same, s, t), i))
    ),
    List.length(&2, Id, Chain.from(~Q, ~view, s, c, Step.ask(~Q, ~view, c, i, ms, r)))
  )
    == Chain.from(~Q, ~view, s, c, Step.ask(~Q, ~view, c, i, ms, r)): List<&2, Id>
}:
  match r:
    case None{}:
      Shared.List.take_zero(
        Id,
        Chain.from(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Step.ask(~Q, ~view, c, i, ms, State.asked(~Q, State.join(~Q, ~same, s, t), i))
        )
      )
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Asked<Q>>,
        State.asked(~Q, State.join(~Q, ~same, s, t), i),
        Some{x},
        Kept.asked(~Q, ~same, ~laws, s, t, i, x, a)(er)
      ):
        {
          List.take(
            &2,
            Id,
            Chain.from(~Q, ~view, State.join(~Q, ~same, s, t), c, Step.ask(~Q, ~view, c, i, ms, _)),
            List.length(&2, Id, Chain.from(~Q, ~view, s, c, Step.ask(~Q, ~view, c, i, ms, Some{x})))
          )
            == Chain.from(~Q, ~view, s, c, Step.ask(~Q, ~view, c, i, ms, Some{x})): List<&2, Id>
        }
      Kept.chain.from(~Q, ~same, ~laws, ~view, s, t, c, a, Step.ask(~Q, ~view, c, i, ms, Some{x}))

# State.chain_kept once the first step mr of the claim is known
def Kept.chain.root(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  mr: Maybe<&2, Step>
) -> {
  List.take(
    &2,
    Id,
    Chain.from(
      ~Q,
      ~view,
      State.join(~Q, ~same, s, t),
      c,
      Chain.root.of(~Q, ~view, State.join(~Q, ~same, s, t), c, mr)
    ),
    List.length(&2, Id, Chain.from(~Q, ~view, s, c, Chain.root.of(~Q, ~view, s, c, mr)))
  )
    == Chain.from(~Q, ~view, s, c, Chain.root.of(~Q, ~view, s, c, mr)): List<&2, Id>
}:
  match mr:
    case None{}:
      {==}
    case Some{Step{+i, ms}}:
      Kept.chain.ask(~Q, ~same, ~laws, ~view, s, t, c, a, i, ms, State.asked(~Q, s, i), {==})

# a chain only grows when no new entry contradicts an old one and its claim
# stays: what a replica answered done stays so after such a sync
law State.chain_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for s: State(Q)
  for t: State(Q)
  for c: List<&2, Bool>
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {
      State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
    }
    -> {
      List.take(
        &2,
        Id,
        State.chain(~Q, ~view, State.join(~Q, ~same, s, t), c),
        List.length(&2, Id, State.chain(~Q, ~view, s, c))
      )
        == State.chain(~Q, ~view, s, c): List<&2, Id>
    }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def State.chain_kept(Q, same, laws, view, s, t, c):
  +s = s
  t = t
  +c = c
  +a => hc =>
    %Equal.sym(
      Maybe<&2, Entry<Q>>,
      State.claim(~Q, State.join(~Q, ~same, s, t), c),
      State.claim(~Q, s, c),
      hc
    ):
      {
        List.take(
          &2,
          Id,
          Chain.from(
            ~Q,
            ~view,
            State.join(~Q, ~same, s, t),
            c,
            Chain.root.of(~Q, ~view, State.join(~Q, ~same, s, t), c, Root.of(~Q, _))
          ),
          List.length(&2, Id, State.chain(~Q, ~view, s, c))
        )
          == State.chain(~Q, ~view, s, c): List<&2, Id>
      }
    Kept.chain.root(~Q, ~same, ~laws, ~view, s, t, c, a, Root.of(~Q, State.claim(~Q, s, c)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Growth
# ------

# a chain of s and t, from its first step st, is the chain of s, then the walk
# of s and t from the last step L of s
def Grow.from(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  st: Step,
  -l: Step,
  el: {
    Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)) == l: Step
  }
) -> {
  Chain.from(
    ~Q,
    ~view,
    State.join(~Q, ~same, s, t),
    c,
    Some{st}
  )
    == List.append(
      &2,
      Id,
      Chain.from(~Q, ~view, s, c, Some{st}),
      Chain.walk(
        ~Q,
        ~view,
        Nat.sub(
          State.fuel(~Q, State.join(~Q, ~same, s, t)),
          List.length(
            &2,
            Id,
            Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, st))
          )
        ),
        State.join(~Q, ~same, s, t),
        c,
        Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l)
      )
    ): List<&2, Id>
}:
  match st:
    case Step{+i, +ms}:
      w = Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, Step{i, ms}))
      g = Nat.sub(State.fuel(~Q, State.join(~Q, ~same, s, t)), List.length(&2, Id, w))
      %el:
        {
          i
            <> Chain.walk(
              ~Q,
              ~view,
              State.fuel(~Q, State.join(~Q, ~same, s, t)),
              State.join(~Q, ~same, s, t),
              c,
              Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, Step{i, ms})
            )
            == i
            <> List.append(
              &2,
              Id,
              w,
              Chain.walk(
                ~Q,
                ~view,
                g,
                State.join(~Q, ~same, s, t),
                c,
                Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, _)
              )
            ): List<&2, Id>
        }
      %Ext.walk(
        ~Q,
        ~same,
        ~laws,
        ~view,
        State.fuel(~Q, s),
        State.fuel(~Q, State.join(~Q, ~same, s, t)),
        s,
        t,
        c,
        Step{i, ms},
        a
      )(State.fuel_le(~Q, ~same, s, t)):
        {
          i
            <> Chain.walk(
              ~Q,
              ~view,
              State.fuel(~Q, State.join(~Q, ~same, s, t)),
              State.join(~Q, ~same, s, t),
              c,
              Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, Step{i, ms})
            )
            == i
            <> _: List<&2, Id>
        }
      {==}

# the last step of s and t, from the first step st, is the last step of the
# walk of s and t from the last step l of s
def Grow.last(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +st: Step,
  -l: Step,
  el: {
    Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)) == l: Step
  }
) -> {
  Chain.last(
    ~Q,
    ~view,
    State.fuel(~Q, State.join(~Q, ~same, s, t)),
    State.join(~Q, ~same, s, t),
    c,
    st,
    Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, st)
  )
    == Chain.last(
      ~Q,
      ~view,
      Nat.sub(
        State.fuel(~Q, State.join(~Q, ~same, s, t)),
        List.length(
          &2,
          Id,
          Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, st))
        )
      ),
      State.join(~Q, ~same, s, t),
      c,
      l,
      Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l)
    ): Step
}:
  g = Nat.sub(
    State.fuel(~Q, State.join(~Q, ~same, s, t)),
    List.length(
      &2,
      Id,
      Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, st))
    )
  )
  %el:
    {
      Chain.last(
        ~Q,
        ~view,
        State.fuel(~Q, State.join(~Q, ~same, s, t)),
        State.join(~Q, ~same, s, t),
        c,
        st,
        Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, st)
      )
        == Chain.last(
          ~Q,
          ~view,
          g,
          State.join(~Q, ~same, s, t),
          c,
          _,
          Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, _)
        ): Step
    }
  Ext.last(
    ~Q,
    ~same,
    ~laws,
    ~view,
    State.fuel(~Q, s),
    State.fuel(~Q, State.join(~Q, ~same, s, t)),
    s,
    t,
    c,
    st,
    a
  )(State.fuel_le(~Q, ~same, s, t))

# a first step of s stays when the claim stays
def Grow.root.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  mr: Maybe<&2, Step>,
  -st: Step
) -> {
  Chain.root.of(~Q, ~view, s, c, mr) == Some{st}: Maybe<&2, Step>
} -> {Chain.root.of(~Q, ~view, State.join(~Q, ~same, s, t), c, mr) == Some{st}: Maybe<&2, Step>}:
  match mr:
    case None{}:
      h => Empty.absurd(
        {
          Chain.root.of(
            ~Q,
            ~view,
            State.join(~Q, ~same, s, t),
            c,
            None{}
          )
            == Some{st}: Maybe<&2, Step>
        },
        Shared.Maybe.none_ne_some(Step, st, h)
      )
    case Some{Step{+i, ms}}:
      Kept.step.ask(~Q, ~same, ~laws, ~view, s, t, c, i, ms, st, a, State.asked(~Q, s, i), {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a first step of s stays in s and t when the claim stays
def Grow.root(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hc: {
    State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
  },
  -st: Step
) -> {
  Chain.root(~Q, ~view, s, c) == Some{st}: Maybe<&2, Step>
} -> {Chain.root(~Q, ~view, State.join(~Q, ~same, s, t), c) == Some{st}: Maybe<&2, Step>}:
  h =>
    %Equal.sym(
      Maybe<&2, Entry<Q>>,
      State.claim(~Q, State.join(~Q, ~same, s, t), c),
      State.claim(~Q, s, c),
      hc
    ):
      {
        Chain.root.of(
          ~Q,
          ~view,
          State.join(~Q, ~same, s, t),
          c,
          Root.of(~Q, _)
        )
          == Some{st}: Maybe<&2, Step>
      }
    Grow.root.of(~Q, ~same, ~laws, ~view, s, t, c, a, Root.of(~Q, State.claim(~Q, s, c)), st)(h)

# a chain whose last step is l has a first step that leads to l, when r is its
# first step
def Start.of(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  c: List<&2, Bool>,
  r: Maybe<&2, Step>,
  -l: Step
) -> {
  Chain.cursor.of(~Q, ~view, s, c, r) == Some{l}: Maybe<&2, Step>
} -> (
  &st: Step -> {
    r == Some{st}: Maybe<&2, Step>
  }
    & {
      Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)) == l: Step
    }
):
  match r:
    case None{}:
      h => Empty.absurd(
        &st: Step -> {
          None{} == Some{st}: Maybe<&2, Step>
        }
          & {
            Chain.last(
              ~Q,
              ~view,
              State.fuel(~Q, s),
              s,
              c,
              st,
              Chain.next(~Q, ~view, s, c, st)
            )
              == l: Step
          },
        Shared.Maybe.none_ne_some(Step, l, h)
      )
    case Some{st}:
      h => (
        st,
        (
          {==},
          Shared.Maybe.some_inj(
            Step,
            Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)),
            l,
            h
          )
        )
      )

# Stay.chain once the first step st of the chain is known
def Stay.chain.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hc: {
    State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
  },
  l: Step,
  en: {Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l) == None{}: Maybe<&2, Step>},
  pr: &st: Step -> {
    Chain.root(~Q, ~view, s, c) == Some{st}: Maybe<&2, Step>
  }
    & {
      Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)) == l: Step
    }
) -> {
  State.chain(
    ~Q,
    ~view,
    State.join(~Q, ~same, s, t),
    c
  )
    == State.chain(~Q, ~view, s, c): List<&2, Id>
}:
  match pr:
    case (+st, (+er, el)):
      +j = State.join(~Q, ~same, s, t)
      g = Nat.sub(
        State.fuel(~Q, j),
        List.length(
          &2,
          Id,
          Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, st))
        )
      )
      x = Chain.from(~Q, ~view, s, c, Some{st})
      Equal.trans(
        List<&2, Id>,
        Chain.from(~Q, ~view, j, c, Chain.root(~Q, ~view, j, c)),
        Chain.from(~Q, ~view, j, c, Some{st}),
        Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c)),
        Equal.cong(
          Maybe<&2, Step>,
          List<&2, Id>,
          z => Chain.from(~Q, ~view, j, c, z),
          Chain.root(~Q, ~view, j, c),
          Some{st},
          Grow.root(~Q, ~same, ~laws, ~view, s, t, c, a, hc, st)(er)
        ),
        Equal.trans(
          List<&2, Id>,
          Chain.from(~Q, ~view, j, c, Some{st}),
          List.append(&2, Id, x, Chain.walk(~Q, ~view, g, j, c, Chain.next(~Q, ~view, j, c, l))),
          Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c)),
          Grow.from(~Q, ~same, ~laws, ~view, s, t, c, a, st, l, el),
          Equal.trans(
            List<&2, Id>,
            List.append(&2, Id, x, Chain.walk(~Q, ~view, g, j, c, Chain.next(~Q, ~view, j, c, l))),
            List.append(&2, Id, x, []),
            Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c)),
            %Equal.sym(Maybe<&2, Step>, Chain.next(~Q, ~view, j, c, l), None{}, en):
              {List.append(&2, Id, x, Chain.walk(~Q, ~view, g, j, c, _)) == List.append(&2, Id, x, []): List<&2, Id>}
            Equal.cong(List<&2, Id>, List<&2, Id>, z => List.append(&2, Id, x, z), Chain.walk(~Q, ~view, g, j, c, None{}), [], Walk.none(~Q, ~view, g, j, c)),
            Equal.trans(List<&2, Id>, List.append(&2, Id, x, []), x, Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c)), Shared.List.append_nil(Id, x), Equal.sym(List<&2, Id>, Chain.from(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c)), x, Equal.cong(Maybe<&2, Step>, List<&2, Id>, z => Chain.from(~Q, ~view, s, c, z), Chain.root(~Q, ~view, s, c), Some{st}, er))))
        )
      )

# a chain stays as it was when nothing follows its last step l in s and t
def Stay.chain(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hc: {
    State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
  },
  l: Step,
  ecur: {Chain.cursor(~Q, ~view, s, c) == Some{l}: Maybe<&2, Step>},
  en: {Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l) == None{}: Maybe<&2, Step>}
) -> {
  State.chain(
    ~Q,
    ~view,
    State.join(~Q, ~same, s, t),
    c
  )
    == State.chain(~Q, ~view, s, c): List<&2, Id>
}:
  Stay.chain.of(
    ~Q,
    ~same,
    ~laws,
    ~view,
    s,
    t,
    c,
    a,
    hc,
    l,
    en,
    Start.of(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c), l)(ecur)
  )

# Stay.cursor once the first step st of the chain is known
def Stay.cursor.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: List<&2, Bool>,
  +a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hc: {
    State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
  },
  l: Step,
  en: {Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l) == None{}: Maybe<&2, Step>},
  pr: &st: Step -> {
    Chain.root(~Q, ~view, s, c) == Some{st}: Maybe<&2, Step>
  }
    & {
      Chain.last(~Q, ~view, State.fuel(~Q, s), s, c, st, Chain.next(~Q, ~view, s, c, st)) == l: Step
    }
) -> {Chain.cursor(~Q, ~view, State.join(~Q, ~same, s, t), c) == Some{l}: Maybe<&2, Step>}:
  match pr:
    case (+st, (er, el)):
      +j = State.join(~Q, ~same, s, t)
      g = Nat.sub(
        State.fuel(~Q, j),
        List.length(
          &2,
          Id,
          Chain.walk(~Q, ~view, State.fuel(~Q, s), s, c, Chain.next(~Q, ~view, s, c, st))
        )
      )
      %Equal.sym(
        Maybe<&2, Step>,
        Chain.root(~Q, ~view, j, c),
        Some{st},
        Grow.root(~Q, ~same, ~laws, ~view, s, t, c, a, hc, st)(er)
      ):
        {Chain.cursor.of(~Q, ~view, j, c, _) == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Step,
        Chain.last(~Q, ~view, State.fuel(~Q, j), j, c, st, Chain.next(~Q, ~view, j, c, st)),
        Chain.last(~Q, ~view, g, j, c, l, Chain.next(~Q, ~view, j, c, l)),
        Grow.last(~Q, ~same, ~laws, ~view, s, t, c, a, st, l, el)
      ):
        {Some{_} == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Maybe<&2, Step>,
        Chain.next(~Q, ~view, j, c, l),
        None{},
        en
      ): {Some{Chain.last(~Q, ~view, g, j, c, l, _)} == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Step,
        Chain.last(~Q, ~view, g, j, c, l, None{}),
        l,
        Last.none(~Q, ~view, g, j, c, l)
      ): {Some{_} == Some{l}: Maybe<&2, Step>}
      {==}

# the last step of a chain stays when nothing follows it in s and t
def Stay.cursor(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  t: State(Q),
  +c: List<&2, Bool>,
  a: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hc: {
    State.claim(~Q, State.join(~Q, ~same, s, t), c) == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
  },
  l: Step,
  ecur: {Chain.cursor(~Q, ~view, s, c) == Some{l}: Maybe<&2, Step>},
  en: {Chain.next(~Q, ~view, State.join(~Q, ~same, s, t), c, l) == None{}: Maybe<&2, Step>}
) -> {Chain.cursor(~Q, ~view, State.join(~Q, ~same, s, t), c) == Some{l}: Maybe<&2, Step>}:
  Stay.cursor.of(
    ~Q,
    ~same,
    ~laws,
    ~view,
    s,
    t,
    c,
    a,
    hc,
    l,
    en,
    Start.of(~Q, ~view, s, c, Chain.root(~Q, ~view, s, c), l)(ecur)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Owner steps
# -----------

# the vote of n at the spot of s is the entry of its slot
def Spot.vote_of(
  ~Q: Data,
  s: State(Q),
  c: List<&2, Bool>,
  v: Id,
  n: String,
  -m: Maybe<&2, Cell<Entry<Q>>>
) -> {
  State.cell(~Q, s, Slot.vote{n, c, v}) == m: Maybe<&2, Cell<Entry<Q>>>
} -> {Spot.vote(~Q, Spot{s, c, v}, n) == Vote.of(~Q, Cell.entry(~Q, m)): Maybe<&2, Id>}:
  h => Equal.cong(
    Maybe<&2, Cell<Entry<Q>>>,
    Maybe<&2, Id>,
    z => Vote.of(~Q, Cell.entry(~Q, z)),
    State.cell(~Q, s, Slot.vote{n, c, v}),
    m,
    h
  )

# nothing follows the step to v when its sole owner n has not voted after it
def Next.none(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: List<&2, Bool>,
  +v: Id,
  +n: String
) -> {
  State.cell(~Q, s, Slot.vote{n, c, v}) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {Chain.next(~Q, ~view, s, c, Step{v, [n]}) == None{}: Maybe<&2, Step>}:
  h =>
    %Equal.sym(
      Maybe<&2, Id>,
      Quorum.winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, [n], [n], Spot{s, c, v}),
      None{},
      Quorum.winner_none(
        ~String,
        ~Id,
        ~Spot<Q>,
        ~Spot.vote(~Q),
        ~Id.same,
        n,
        Spot{s, c, v}
      )(Spot.vote_of(~Q, s, c, v, n, None{})(h))
    ):
      {Step.won(~Q, ~view, s, c, [n], _) == None{}: Maybe<&2, Step>}
    {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the version i follows v when its sole owner n voted for it, and its change q
# is on the chain
def Next.one(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: List<&2, Bool>,
  +v: Id,
  +n: String,
  i: Id,
  t: String,
  q: Q
) -> {
  State.cell(~Q, s, Slot.vote{n, c, v}) == Some{one{Entry.vote{i}}}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  State.asked(~Q, s, i) == Some{Asked{t, q}}: Maybe<&2, Asked<Q>>
} -> {
  Key.same(View.chain(view(q)), c) == True{}: Bool
} -> {
  Chain.next(
    ~Q,
    ~view,
    s,
    c,
    Step{v, [n]}
  )
    == Some{Step{i, View.owners_of(view(q), [n])}}: Maybe<&2, Step>
}:
  hv => ha => hq =>
    %Equal.sym(
      Maybe<&2, Id>,
      Quorum.winner(~String, ~Id, ~Spot<Q>, ~Spot.vote(~Q), ~Id.same, [n], [n], Spot{s, c, v}),
      Some{i},
      Quorum.winner_one(
        ~String,
        ~Id,
        ~Spot<Q>,
        ~Spot.vote(~Q),
        ~Id.same,
        ~Id.laws(),
        n,
        Spot{s, c, v},
        i
      )(Spot.vote_of(~Q, s, c, v, n, Some{one{Entry.vote{i}}})(hv))
    ):
      {
        Step.won(
          ~Q,
          ~view,
          s,
          c,
          [n],
          _
        )
          == Some{Step{i, View.owners_of(view(q), [n])}}: Maybe<&2, Step>
      }
    %Equal.sym(Maybe<&2, Asked<Q>>, State.asked(~Q, s, i), Some{Asked{t, q}}, ha):
      {
        Step.ask(
          ~Q,
          ~view,
          c,
          i,
          [n],
          _
        )
          == Some{Step{i, View.owners_of(view(q), [n])}}: Maybe<&2, Step>
      }
    %Equal.sym(Bool, Key.same(View.chain(view(q)), c), True{}, hq):
      {
        Step.if(
          ~Q,
          ~view,
          _,
          i,
          q,
          [n]
        )
          == Some{Step{i, View.owners_of(view(q), [n])}}: Maybe<&2, Step>
      }
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the last step of a chain with the head v and the sole owner n is the step to v
def Owner.cursor(
  +m: Maybe<&2, Step>,
  n: String,
  v: Id
) -> {
  Step.owners.of(m) == [n]: List<&2, String>
} -> {
  Maybe.map(&2, Step, Id, k => Step.version(k), m) == Some{v}: Maybe<&2, Id>
} -> {m == Some{Step{v, [n]}}: Maybe<&2, Step>}:
  match m:
    case None{}:
      ho => hh => Empty.absurd(
        {None{} == Some{Step{v, [n]}}: Maybe<&2, Step>},
        Shared.Maybe.none_ne_some(Id, v, hh)
      )
    case Some{Step{kv, kms}}:
      ho => hh =>
        %Shared.Maybe.some_inj(
          Id,
          kv,
          v,
          hh
        ): {Some{Step{kv, kms}} == Some{Step{_, [n]}}: Maybe<&2, Step>}
        %ho: {Some{Step{kv, kms}} == Some{Step{kv, _}}: Maybe<&2, Step>}
        {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a chain that has a last step has a claim
def Claim.of(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  c: List<&2, Bool>,
  m: Maybe<&2, Entry<Q>>,
  em: {State.claim(~Q, s, c) == m: Maybe<&2, Entry<Q>>},
  -l: Step
) -> {
  Chain.cursor(~Q, ~view, s, c) == Some{l}: Maybe<&2, Step>
} -> (&x: Entry<Q> -> {m == Some{x}: Maybe<&2, Entry<Q>>}):
  match m:
    case None{}:
      h => Empty.absurd(
        &x: Entry<Q> -> {None{} == Some{x}: Maybe<&2, Entry<Q>>},
        Shared.Maybe.none_ne_some(
          Step,
          l,
          Equal.trans(
            Maybe<&2, Step>,
            None{},
            Chain.cursor(~Q, ~view, s, c),
            Some{l},
            Equal.sym(
              Maybe<&2, Step>,
              Chain.cursor(~Q, ~view, s, c),
              None{},
              Equal.cong(
                Maybe<&2, Entry<Q>>,
                Maybe<&2, Step>,
                z => Chain.cursor.of(
                  ~Q,
                  ~view,
                  s,
                  c,
                  Chain.root.of(~Q, ~view, s, c, Root.of(~Q, z))
                ),
                State.claim(~Q, s, c),
                None{},
                em
              )
            ),
            h
          )
        )
      )
    case Some{x}:
      h => (x, {==})
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a node that took in a new request q of i at the time t, whose chain has the
# claim m, votes or not as State.ask.at says
def Owner.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~fits: State(Q) -> Q -> Id -> Bool,
  n: String,
  s: State(Q),
  i: Id,
  t: String,
  q: Q,
  m: Maybe<&2, Entry<Q>>,
  hm: &x: Entry<Q> -> {m == Some{x}: Maybe<&2, Entry<Q>>}
) -> {
  State.ask.root(
    ~Q,
    ~same,
    ~view,
    ~fits,
    n,
    s,
    State.put(~Q, ~same, s, Slot.ask{i}, Entry.ask{i, t, q}),
    i,
    q,
    m
  )
    == State.ask.at(
      ~Q,
      ~same,
      ~view,
      ~fits,
      n,
      s,
      State.put(~Q, ~same, s, Slot.ask{i}, Entry.ask{i, t, q}),
      i,
      q,
      Chain.cursor(~Q, ~view, s, View.chain(view(q)))
    ): State(Q)
}:
  match hm:
    case (x, ex):
      %Equal.sym(Maybe<&2, Entry<Q>>, m, Some{x}, ex):
        {
          State.ask.root(
            ~Q,
            ~same,
            ~view,
            ~fits,
            n,
            s,
            State.put(~Q, ~same, s, Slot.ask{i}, Entry.ask{i, t, q}),
            i,
            q,
            _
          )
            == State.ask.at(
              ~Q,
              ~same,
              ~view,
              ~fits,
              n,
              s,
              State.put(~Q, ~same, s, Slot.ask{i}, Entry.ask{i, t, q}),
              i,
              q,
              Chain.cursor(~Q, ~view, s, View.chain(view(q)))
            ): State(Q)
        }
      {==}

# the cell of s and one entry at k, at a key p apart from k, is the cell of s
def Fresh.cell(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  +p: List<&2, Bool>,
  +x: Cell<Entry<Q>>
) -> {
  Shared.Trie.apart(k, p) == True{}: Bool
} -> {
  Shared.Trie.get(
    Cell<Entry<Q>>,
    State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x)),
    p
  )
    == Shared.Trie.get(Cell<Entry<Q>>, s, p): Maybe<&2, Cell<Entry<Q>>>
}:
  ap =>
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Shared.Trie.get(
        Cell<Entry<Q>>,
        State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x)),
        p
      ),
      Shared.Trie.pick(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
        Shared.Trie.get(Cell<Entry<Q>>, s, p),
        Shared.Trie.get(Cell<Entry<Q>>, Shared.Trie.one(Cell<Entry<Q>>, k, x), p)
      ),
      Shared.Trie.get_union(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
        s,
        Shared.Trie.one(Cell<Entry<Q>>, k, x),
        p
      )
    ):
      {_ == Shared.Trie.get(Cell<Entry<Q>>, s, p): Maybe<&2, Cell<Entry<Q>>>}
    %Equal.sym(
      Maybe<&2, Cell<Entry<Q>>>,
      Shared.Trie.get(Cell<Entry<Q>>, Shared.Trie.one(Cell<Entry<Q>>, k, x), p),
      None{},
      Shared.Trie.get_one_apart(Cell<Entry<Q>>, k, p, x)(ap)
    ):
      {
        Shared.Trie.pick(
          ~Cell<Entry<Q>>,
          ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
          Shared.Trie.get(Cell<Entry<Q>>, s, p),
          _
        )
          == Shared.Trie.get(Cell<Entry<Q>>, s, p): Maybe<&2, Cell<Entry<Q>>>
      }
    Shared.Trie.pick_none(
      ~Cell<Entry<Q>>,
      ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
      Shared.Trie.get(Cell<Entry<Q>>, s, p)
    )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the claim of a chain stays when one entry joins apart from its roots
def Fresh.claim(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  c: List<&2, Bool>,
  x: Cell<Entry<Q>>
) -> {
  Shared.Trie.apart(k, Root.key(c)) == True{}: Bool
} -> {
  State.claim(
    ~Q,
    State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x)),
    c
  )
    == State.claim(~Q, s, c): Maybe<&2, Entry<Q>>
}:
  ap => Equal.cong(
    Shared.Trie<Cell<Entry<Q>>>,
    Maybe<&2, Entry<Q>>,
    z => Root.first(~Q, Shared.Trie.values(Cell<Entry<Q>>, z)),
    Shared.Trie.under(
      Cell<Entry<Q>>,
      State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x)),
      Root.key(c)
    ),
    Shared.Trie.under(Cell<Entry<Q>>, s, Root.key(c)),
    Shared.Trie.under_union_apart(
      ~Cell<Entry<Q>>,
      ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
      s,
      k,
      Root.key(c),
      x
    )(ap)
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# the sole owner n of the chain of q refuses a request i of q that does not
# fit the head v: the chain stays as it was
law State.chain_after_unfit_ask:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~fits: State(Q) -> Q -> Id -> Bool
  for n: String
  for s: State(Q)
  for i: Id
  for t: String
  for q: Q
  for v: Id
  {State.owners(~Q, ~view, s, View.chain(view(q))) == [n]: List<&2, String>}
    -> {State.head(~Q, ~view, s, View.chain(view(q))) == Some{v}: Maybe<&2, Id>}
    -> {State.cell(~Q, s, Slot.ask{i}) == None{}: Maybe<&2, Cell<Entry<Q>>>}
    -> {
      State.cell(~Q, s, Slot.vote{n, View.chain(view(q)), v}) == None{}: Maybe<&2, Cell<Entry<Q>>>
    }
    -> {fits(s, q, v) == False{}: Bool}
    -> {
      State.chain(
        ~Q,
        ~view,
        State.ask(~Q, ~same, ~view, ~fits, n, s, i, t, q),
        View.chain(view(q))
      )
        == State.chain(~Q, ~view, s, View.chain(view(q))): List<&2, Id>
    }

def State.chain_after_unfit_ask(Q, same, laws, view, fits, n, s, i, t, q, v):
  +n = n
  +s = s
  +i = i
  +t = t
  +q = q
  +v = v
  +c = View.chain(view(q))
  l = {Step{v, [n]}: Step}
  +ka = Slot.key(Slot.ask{i})
  kv = Slot.key(Slot.vote{n, c, v})
  +ea = {one{Entry.ask{i, t, q}}: Cell<Entry<Q>>}
  +ta = Shared.Trie.one(Cell<Entry<Q>>, ka, ea)
  s1 = State.join(~Q, ~same, s, ta)
  +h1 => +h2 => +h3 => +h4 => hf =>
    +ecur = Owner.cursor(Chain.cursor(~Q, ~view, s, c), n, v)(h1)(h2)
    +a = Cell.agrees_one(~Entry<Q>, ~Entry.same(~Q, ~same), s, ka, ea)(h3)
    +hc = Fresh.claim(~Q, ~same, s, ka, c, ea)({==})
    +f4 = Equal.trans(
      Maybe<&2, Cell<Entry<Q>>>,
      Shared.Trie.get(Cell<Entry<Q>>, s1, kv),
      Shared.Trie.get(Cell<Entry<Q>>, s, kv),
      None{},
      Fresh.cell(~Q, ~same, s, ka, kv, ea)({==}),
      h4
    )
    +kept = Stay.chain(
      ~Q,
      ~same,
      ~laws,
      ~view,
      s,
      ta,
      c,
      a,
      hc,
      l,
      ecur,
      Next.none(~Q, ~view, s1, c, v, n)(f4)
    )
    +may = State.may_vote(~Q, n, s, c, v, [n])
    +ask = Equal.trans(
      State(Q),
      State.ask(~Q, ~same, ~view, ~fits, n, s, i, t, q),
      State.ask.root(~Q, ~same, ~view, ~fits, n, s, s1, i, q, State.claim(~Q, s, c)),
      s1,
      Equal.cong(
        Maybe<&2, Cell<Entry<Q>>>,
        State(Q),
        z => State.ask.fresh(~Q, ~same, ~view, ~fits, n, s, i, t, q, z),
        State.cell(~Q, s, Slot.ask{i}),
        None{},
        h3
      ),
      Equal.trans(
        State(Q),
        State.ask.root(~Q, ~same, ~view, ~fits, n, s, s1, i, q, State.claim(~Q, s, c)),
        State.ask.at(~Q, ~same, ~view, ~fits, n, s, s1, i, q, Chain.cursor(~Q, ~view, s, c)),
        s1,
        Owner.ask(
          ~Q,
          ~same,
          ~view,
          ~fits,
          n,
          s,
          i,
          t,
          q,
          State.claim(~Q, s, c),
          Claim.of(~Q, ~view, s, c, State.claim(~Q, s, c), {==}, l)(ecur)
        ),
        Equal.trans(
          State(Q),
          State.ask.at(~Q, ~same, ~view, ~fits, n, s, s1, i, q, Chain.cursor(~Q, ~view, s, c)),
          State.ask.at(~Q, ~same, ~view, ~fits, n, s, s1, i, q, Some{l}),
          s1,
          Equal.cong(
            Maybe<&2, Step>,
            State(Q),
            z => State.ask.at(~Q, ~same, ~view, ~fits, n, s, s1, i, q, z),
            Chain.cursor(~Q, ~view, s, c),
            Some{l},
            ecur
          ),
          Equal.cong(
            Bool,
            State(Q),
            z => Bool.pick(
              State(Q),
              z,
              State.put(~Q, ~same, s1, Slot.vote{n, c, v}, Entry.vote{i}),
              s1
            ),
            Bool.and(may, fits(s, q, v)),
            False{},
            Equal.trans(
              Bool,
              Bool.and(may, fits(s, q, v)),
              Bool.and(may, False{}),
              False{},
              Equal.cong(Bool, Bool, z => Bool.and(may, z), fits(s, q, v), False{}, hf),
              Shared.Bool.and_false_right(may)
            )
          )
        )
      )
    )
    Equal.trans(
      List<&2, Id>,
      State.chain(~Q, ~view, State.ask(~Q, ~same, ~view, ~fits, n, s, i, t, q), c),
      State.chain(~Q, ~view, s1, c),
      State.chain(~Q, ~view, s, c),
      Equal.cong(
        State(Q),
        List<&2, Id>,
        z => State.chain(~Q, ~view, z, c),
        State.ask(~Q, ~same, ~view, ~fits, n, s, i, t, q),
        s1,
        ask
      ),
      kept
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a list that holds a node holds it
def Owners.has(n: String) -> {List.contains(~String, ~String.eq, [n], n) == True{}: Bool}:
  %Equal.sym(Bool, String.eq(n, n), True{}, Shared.String.eq_refl(n)):
    {List.any.if(u => List.contains(~String, ~String.eq, [], n), _) == True{}: Bool}
  {==}

# one entry at a free key walks one step further
def Grow.fuel(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  k: List<&2, Bool>,
  x: Cell<Entry<Q>>
) -> {
  Shared.Trie.get(Cell<Entry<Q>>, s, k) == None{}: Maybe<&2, Cell<Entry<Q>>>
} -> {
  Nat.is_lt(
    State.fuel(~Q, s),
    State.fuel(~Q, State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x)))
  )
    == True{}: Bool
}:
  h =>
    %Equal.sym(
      Nat,
      Shared.Trie.size(
        Cell<Entry<Q>>,
        State.join(~Q, ~same, s, Shared.Trie.one(Cell<Entry<Q>>, k, x))
      ),
      1n+Shared.Trie.size(Cell<Entry<Q>>, s),
      Shared.Trie.size_union_one(
        ~Cell<Entry<Q>>,
        ~Cell.join(~Entry<Q>, ~Entry.same(~Q, ~same)),
        s,
        k,
        x
      )(h)
    ):
      {Nat.is_lt(State.fuel(~Q, s), 1n+_) == True{}: Bool}
    Shared.Nat.lt_succ(Shared.Trie.size(Cell<Entry<Q>>, s))

# the request i is in the chain of s2, s1 and the sole owner's vote for it
# after v, once the first step of the chain of s1 is known
def Owner.puts(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  n: String,
  +s1: State(Q),
  +i: Id,
  +c: List<&2, Bool>,
  v: Id,
  +tv: State(Q),
  +a2: {State.agrees(~Q, ~same, s1, tv) == True{}: Bool},
  hc2: {
    State.claim(~Q, State.join(~Q, ~same, s1, tv), c) == State.claim(~Q, s1, c): Maybe<&2, Entry<Q>>
  },
  next2: {
    Chain.next(
      ~Q,
      ~view,
      State.join(~Q, ~same, s1, tv),
      c,
      Step{v, [n]}
    )
      == Some{Step{i, [n]}}: Maybe<&2, Step>
  },
  grow: {
    Nat.is_lt(State.fuel(~Q, s1), State.fuel(~Q, State.join(~Q, ~same, s1, tv))) == True{}: Bool
  },
  pr: &st: Step -> {
    Chain.root(~Q, ~view, s1, c) == Some{st}: Maybe<&2, Step>
  }
    & {
      Chain.last(
        ~Q,
        ~view,
        State.fuel(~Q, s1),
        s1,
        c,
        st,
        Chain.next(~Q, ~view, s1, c, st)
      )
        == Step{v, [n]}: Step
    }
) -> {
  List.contains(
    ~Id,
    ~Id.same,
    State.chain(~Q, ~view, State.join(~Q, ~same, s1, tv), c),
    i
  )
    == True{}: Bool
}:
  match pr:
    case (+st, (er, el)):
      +s2 = State.join(~Q, ~same, s1, tv)
      +w1 = Chain.walk(~Q, ~view, State.fuel(~Q, s1), s1, c, Chain.next(~Q, ~view, s1, c, st))
      x1 = Chain.from(~Q, ~view, s1, c, Some{st})
      g = Nat.sub(State.fuel(~Q, s2), List.length(&2, Id, w1))
      g1 = Nat.sub(State.fuel(~Q, s2), 1n+List.length(&2, Id, w1))
      rest = Chain.walk(~Q, ~view, g1, s2, c, Chain.next(~Q, ~view, s2, c, Step{i, [n]}))
      gs = Shared.Nat.sub_pos(
        List.length(&2, Id, w1),
        State.fuel(~Q, s2)
      )(
        Shared.Nat.le_lt(
          List.length(&2, Id, w1),
          State.fuel(~Q, s1),
          State.fuel(~Q, s2)
        )(Walk.length(~Q, ~view, State.fuel(~Q, s1), s1, c, Chain.next(~Q, ~view, s1, c, st)))(grow)
      )
      shape = Equal.trans(
        List<&2, Id>,
        Chain.from(~Q, ~view, s2, c, Chain.root(~Q, ~view, s2, c)),
        Chain.from(~Q, ~view, s2, c, Some{st}),
        List.append(&2, Id, x1, i <> rest),
        Equal.cong(
          Maybe<&2, Step>,
          List<&2, Id>,
          z => Chain.from(~Q, ~view, s2, c, z),
          Chain.root(~Q, ~view, s2, c),
          Some{st},
          Grow.root(~Q, ~same, ~laws, ~view, s1, tv, c, a2, hc2, st)(er)
        ),
        Equal.trans(
          List<&2, Id>,
          Chain.from(~Q, ~view, s2, c, Some{st}),
          List.append(&2, Id, x1, Chain.walk(~Q, ~view, g, s2, c, Chain.next(~Q, ~view, s2, c, Step{v, [n]}))),
          List.append(&2, Id, x1, i <> rest),
          Grow.from(~Q, ~same, ~laws, ~view, s1, tv, c, a2, st, Step{v, [n]}, el),
          %Equal.sym(Maybe<&2, Step>, Chain.next(~Q, ~view, s2, c, Step{v, [n]}), Some{Step{i, [n]}}, next2):
            {List.append(&2, Id, x1, Chain.walk(~Q, ~view, g, s2, c, _)) == List.append(&2, Id, x1, i <> rest): List<&2, Id>}
          %Equal.sym(Nat, g, 1n+g1, gs):
            {List.append(&2, Id, x1, Chain.walk(~Q, ~view, _, s2, c, Some{Step{i, [n]}})) == List.append(&2, Id, x1, i <> rest): List<&2, Id>}
          {==})
      )
      %Equal.sym(
        List<&2, Id>,
        State.chain(~Q, ~view, s2, c),
        List.append(&2, Id, x1, i <> rest),
        shape
      ):
        {List.contains(~Id, ~Id.same, _, i) == True{}: Bool}
      Shared.List.contains_middle(~Id, ~Id.same, ~Id.laws(), x1, i, rest)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
