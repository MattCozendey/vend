import Base

# Comparisons
# -----------

# c, unless it is EQ: then rest
def Cmp.then(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      rest
    case GT{}:
      GT{}

# c seen from the other side: LT and GT swap
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# Lists of words
# --------------
# Lists of words are ordered word by word. A list that is a prefix of another
# comes first.

# how the list of words a compares with the list of words b
def Words.cmp(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, ys}:
      LT{}
    case Con{x, xs} Nil{}:
      GT{}
    case Con{x, xs} Con{y, ys}:
      Cmp.then(U32.cmp(x, y), Words.cmp(xs, ys))

# Means: comparing a list of words with itself gives "equal", and comparing two
# lists of words gives "equal" only when they are the same list.
# For free: a key can be found by comparing keys alone; two different keys never
# land on one entry.
# For the goal: a map keyed by lists of words holds one entry per key, so a
# fact is held once, however often it arrives.
# Example: [1, 2] and [1, 2] compare equal; [1, 2] and [1, 3] do not.
law Words.cmp_equal:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Words.cmp(a, a) == EQ{}: Cmp} & ({Words.cmp(a, b) == EQ{}: Cmp} -> {a == b: List<&2, U32>})

# Means: comparing b with a gives the other side of comparing a with b: "below"
# becomes "above", and "equal" stays.
# For free: one comparison answers both questions; "above" needs no law of its
# own.
# For the goal: a split at a key and the order of a list agree from both sides.
# Example: [1] is below [2], so [2] is above [1].
law Words.cmp_flips:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Words.cmp(b, a) == Cmp.flip(Words.cmp(a, b)): Cmp}

# Means: if a is below b, and b is below c, then a is below c.
# For free: a list whose neighbours go up goes up as a whole; "below" never
# loops.
# For the goal: a map can check its order one pair of neighbours at a time,
# and a split is right for every key on each side.
# Example: [1] is below [2], and [2] is below [3], so [1] is below [3].
law Words.below_transitive:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for c: List<&2, U32>
  {Words.cmp(a, b) == LT{}: Cmp} -> {Words.cmp(b, c) == LT{}: Cmp} -> {Words.cmp(a, c) == LT{}: Cmp}

# Optional values
# ---------------

# x and y combined by both when each is there, else the one that is there
def Maybe.merge(~A: Data, ~both: A -> A -> A, x: Maybe<&2, A>, y: Maybe<&2, A>) -> Maybe<&2, A>:
  match x y:
    case Some{a} Some{b}:
      Some{both(a, b)}
    case Some{a} None{}:
      Some{a}
    case None{} y:
      y

# x when c holds, else nothing
def Maybe.when(~A: Data, c: Bool, x: Maybe<&2, A>) -> Maybe<&2, A>:
  Bool.pick(Maybe<&2, A>, c, x, None{})

# Lists of pairs
# --------------
# A pair is a key (a list of words) and its value.

# the value x of the key k, if it is there and the pair passes the test
def Pairs.keep(
  ~V: Data,
  ~test: List<&2, U32> -> V -> Bool,
  k: List<&2, U32>,
  x: Maybe<&2, V>
) -> Maybe<&2, V>:
  match x:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, V>, test(k, v), Some{v}, None{})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: no code that runs calls Pairs.first or Pairs.ascend, so what they compute in excess costs nothing
# the value of the first pair of xs whose key is k, if any
def Pairs.first(
  ~V: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => V>>,
  +k: List<&2, U32>
) -> Maybe<&2, V>:
  match xs:
    case Nil{}:
      None{}
    case Con{(key, v), rest}:
      Bool.pick(Maybe<&2, V>, Cmp.is_eq(Words.cmp(key, k)), Some{v}, Pairs.first(~V, rest, k))

# the key k comes before the key of the first pair of xs, if any
def Pairs.ascend.next(
  ~V: Data,
  k: List<&2, U32>,
  xs: List<&2, +Sigma<List<&2, U32>, _ => V>>
) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(j, w), rest}:
      Cmp.is_lt(Words.cmp(k, j))

# the keys of xs go up strictly, one pair after another
def Pairs.ascend(~V: Data, xs: List<&2, +Sigma<List<&2, U32>, _ => V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(k, v), +rest}:
      Bool.and(Pairs.ascend.next(~V, k, rest), Pairs.ascend(~V, rest))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# m combined with s, if any
def Pairs.fold.join(~M: Data, ~combine: M -> M -> M, m: M, s: Maybe<&2, M>) -> M:
  match s:
    case None{}:
      m
    case Some{x}:
      combine(m, x)

# the measures of the pairs of xs, combined in order; nothing if xs is empty
def Pairs.fold(
  ~V: Data,
  ~M: Data,
  ~of: List<&2, U32> -> V -> M,
  ~combine: M -> M -> M,
  xs: List<&2, +Sigma<List<&2, U32>, _ => V>>
) -> Maybe<&2, M>:
  match xs:
    case Nil{}:
      None{}
    case Con{(k, v), rest}:
      Some{Pairs.fold.join(~M, ~combine, of(k, v), Pairs.fold(~V, ~M, ~of, ~combine, rest))}
