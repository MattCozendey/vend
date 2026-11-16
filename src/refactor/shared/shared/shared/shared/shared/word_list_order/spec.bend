import Base
import ../shared.bend as Shared

# Lists of words
# --------------
# Lists of words are ordered word by word. A list that is a prefix of another
# comes first.

# how the list of words a compares with the list of words b
def cmp(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, ys}:
      LT{}
    case Con{x, xs} Nil{}:
      GT{}
    case Con{x, xs} Con{y, ys}:
      Shared.Cmp.then(U32.cmp(x, y), cmp(xs, ys))

# Means: comparing a list of words with itself gives "equal", and comparing two
# lists of words gives "equal" only when they are the same list.
# For free: a key can be found by comparing keys alone; two different keys never
# land on one entry.
# For the goal: a map keyed by lists of words holds one entry per key, so a
# record is held once, however often it arrives.
# Example: [1, 2] and [1, 2] compare equal; [1, 2] and [1, 3] do not.
law cmp_equal:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {cmp(a, a) == EQ{}: Cmp} & ({cmp(a, b) == EQ{}: Cmp} -> {a == b: List<&2, U32>})

# Means: comparing b with a gives the other side of comparing a with b: "below"
# becomes "above", and "equal" stays.
# For free: one comparison answers both questions; "above" needs no law of its
# own.
# For the goal: a split at a key and the order of a list agree from both sides.
# Example: [1] is below [2], so [2] is above [1].
law cmp_flips:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {cmp(b, a) == Shared.Cmp.flip(cmp(a, b)): Cmp}

# Means: if a is below b, and b is below c, then a is below c.
# For free: a list whose neighbours go up goes up as a whole; "below" never
# loops.
# For the goal: a map can check its order one pair of neighbours at a time,
# and a split is right for every key on each side.
# Example: [1] is below [2], and [2] is below [3], so [1] is below [3].
law below_transitive:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for c: List<&2, U32>
  {cmp(a, b) == LT{}: Cmp} -> {cmp(b, c) == LT{}: Cmp} -> {cmp(a, c) == LT{}: Cmp}

# the highest bit that is set in d, alone; 0 when d is 0
def highest_bit(+d: U32) -> U32:
  +a = U32.or(d, U32.shrn(d, 1n))
  +b = U32.or(a, U32.shrn(a, 2n))
  +c = U32.or(b, U32.shrn(b, 4n))
  +e = U32.or(c, U32.shrn(c, 8n))
  +f = U32.or(e, U32.shrn(e, 16n))
  U32.sub(f, U32.shrn(f, 1n))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the call that Bool.pick does not need walks the rest of two keys once, and a key is a few words
# Seen as bits, a list of words is, for each word, a 1 and then the 32 bits of
# the word, highest first, and then a 0. These bits are ordered as cmp
# orders the lists. For two lists a below b, the split key is the smallest list
# whose bits agree with a and b before the first bit where a and b differ, and
# whose bit there is 1: the lists from a to the split key, below it, have a 0
# there, and those from the split key to b have a 1.
def split_key(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
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
        x <> split_key(xs, ys),
        [U32.and(y, U32.not(U32.sub(highest_bit(U32.xor(x, y)), 1)))]
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Means: for two lists of words a below b, a is below their split key, and the
# split key is at or below b.
# For free: splitting at the split key of a and b puts a on one side and b on
# the other, so neither side is empty and each is smaller than the whole.
# For the goal: the summary law of patricia_map splits a map of two or more
# entries into two smaller maps, so a summary is a real Merkle hash of two
# halves, not an equation that any value meets.
# Example: [1, 5] and [1, 9] first differ at the bit worth 8 in their second
# words, so their split key is [1, 8], with [1, 5] below it and [1, 9] above.
law split_key_between:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {cmp(a, b) == LT{}: Cmp}
    -> {
      cmp(a, split_key(a, b)) == LT{}: Cmp
    }
      & {Cmp.is_gt(cmp(split_key(a, b), b)) == False{}: Bool}
