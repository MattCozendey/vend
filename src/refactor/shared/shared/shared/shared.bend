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

# the highest bit that is set in d, alone; 0 when d is 0
def Word.top(+d: U32) -> U32:
  +a = U32.or(d, U32.shrn(d, 1n))
  +b = U32.or(a, U32.shrn(a, 2n))
  +c = U32.or(b, U32.shrn(b, 4n))
  +e = U32.or(c, U32.shrn(c, 8n))
  +f = U32.or(e, U32.shrn(e, 16n))
  U32.sub(f, U32.shrn(f, 1n))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the call that Bool.pick does not need walks the rest of two keys once, and a key is a few words
# Seen as bits, a list of words is, for each word, a 1 and then the 32 bits of
# the word, highest first, and then a 0. These bits are ordered as Words.cmp
# orders the lists. For two lists a below b, the split key is the smallest list
# whose bits agree with a and b before the first bit where a and b differ, and
# whose bit there is 1: the lists from a to the split key, below it, have a 0
# there, and those from the split key to b have a 1.
def Words.split_key(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, ys}:
      [0]
    case Con{x, xs} Nil{}:
      []
    case Con{+x, xs} Con{+y, ys}:
      Bool.pick(
        List<&2, U32>,
        U32.is_eq(x, y),
        x <> Words.split_key(xs, ys),
        [U32.and(y, U32.not(U32.sub(Word.top(U32.xor(x, y)), 1)))]
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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

# the key of the last pair of xs, or k when xs is empty
def Pairs.last_key(
  ~V: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => V>>,
  k: List<&2, U32>
) -> List<&2, U32>:
  match xs:
    case Nil{}:
      k
    case Con{(j, w), rest}:
      Pairs.last_key(~V, rest, j)

# Rows
# ----

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- Row is a type: it is used only in types and erased arguments, so no code that runs builds or frees its binder
# n values of A in a row
def Row(-A: Data, n: Nat) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+m:
      +Sigma<A, _ => Row(A, m)>
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
