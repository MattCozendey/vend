import Base
import ../shared/word_list_order/spec.bend as WordListOrder

# Lists of pairs
# --------------
# A pair is a key (a list of words) and its value.

# the value x of the key k, if it is there and the pair passes the test
def value_if_entry_passes(
  ~Value: Data,
  ~keeps_entry: List<&2, U32> -> Value -> Bool,
  k: List<&2, U32>,
  x: Maybe<&2, Value>
) -> Maybe<&2, Value>:
  match x:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, Value>, keeps_entry(k, v), Some{v}, None{})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: no code that runs calls value_of_first_entry_with_key or keys_strictly_increase, so what they compute in excess costs nothing
# the value of the first pair of xs whose key is k, if any
def value_of_first_entry_with_key(
  ~Value: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>,
  +k: List<&2, U32>
) -> Maybe<&2, Value>:
  match xs:
    case Nil{}:
      None{}
    case Con{(key, v), rest}:
      Bool.pick(
        Maybe<&2, Value>,
        Cmp.is_eq(WordListOrder.cmp(key, k)),
        Some{v},
        value_of_first_entry_with_key(~Value, rest, k)
      )

# the key k comes before the key of the first pair of xs, if any
def keys_strictly_increase.next(
  ~Value: Data,
  k: List<&2, U32>,
  xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>
) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(j, w), rest}:
      Cmp.is_lt(WordListOrder.cmp(k, j))

# the keys of xs go up strictly, one pair after another
def keys_strictly_increase(~Value: Data, xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(k, v), +rest}:
      Bool.and(keys_strictly_increase.next(~Value, k, rest), keys_strictly_increase(~Value, rest))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the key of the last pair of xs, or k when xs is empty
def key_of_last_entry(
  ~Value: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>,
  k: List<&2, U32>
) -> List<&2, U32>:
  match xs:
    case Nil{}:
      k
    case Con{(j, w), rest}:
      key_of_last_entry(~Value, rest, j)

# the keys of the pairs xs, in order
def keys(~Value: Data, xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      []
    case Con{(k, v), rest}:
      k <> keys(~Value, rest)

# the pairs ys, after the key k with the value x when x is there
def with_entry.put(
  ~Value: Data,
  k: List<&2, U32>,
  x: Maybe<&2, Value>,
  ys: List<&2, +Sigma<List<&2, U32>, _ => Value>>
) -> List<&2, +Sigma<List<&2, U32>, _ => Value>>:
  match x:
    case None{}:
      ys
    case Some{v}:
      (k, v) <> ys

# the key of the first pair of xs is below the key k
def with_entry.below(
  ~Value: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>,
  k: List<&2, U32>
) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{(j, w), rest}:
      Cmp.is_lt(WordListOrder.cmp(j, k))

# the pairs after the key k, from the first pair (j, w) of a list whose other
# pairs are rest, where j is not below k: rest when j is k, else all of them
def with_entry.after(
  ~Value: Data,
  replaced: Bool,
  j: List<&2, U32>,
  w: Value,
  rest: List<&2, +Sigma<List<&2, U32>, _ => Value>>
) -> List<&2, +Sigma<List<&2, U32>, _ => Value>>:
  match replaced:
    case True{}:
      rest
    case False{}:
      (j, w) <> rest

# the pairs xs with the key k set to x (none: removed), where below says
# whether the key of the first pair of xs is below k: the pairs below k stay in
# front, the pair of k is replaced, and the pairs above k stay after it
def with_entry.go(
  ~Value: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>,
  +k: List<&2, U32>,
  x: Maybe<&2, Value>,
  below: Bool
) -> List<&2, +Sigma<List<&2, U32>, _ => Value>>:
  match xs:
    case Nil{}:
      with_entry.put(~Value, k, x, [])
    case Con{(+j, w), +rest}:
      match below:
        case True{}:
          (j, w) <> with_entry.go(~Value, rest, k, x, with_entry.below(~Value, rest, k))
        case False{}:
          with_entry.put(
            ~Value,
            k,
            x,
            with_entry.after(~Value, Cmp.is_eq(WordListOrder.cmp(j, k)), j, w, rest)
          )

# the pairs xs with the key k set to x (none: removed), in key order
def with_entry(
  ~Value: Data,
  +xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>,
  +k: List<&2, U32>,
  x: Maybe<&2, Value>
) -> List<&2, +Sigma<List<&2, U32>, _ => Value>>:
  with_entry.go(~Value, xs, k, x, with_entry.below(~Value, xs, k))

# Laws
# ----

# Means: in pairs whose keys go up strictly, setting the key k to x (none:
# removing it) keeps the keys going up strictly, gives x at k, and leaves the
# value of every other key as it was.
# For free: pairs kept in key order are one list for one set of pairs, so two
# maps with the same pairs are equal, whatever order the pairs were set in;
# setting a key twice keeps the last value; removing a missing key changes
# nothing.
# For the goal: the contents of versions, and the marks of a branch, are pairs
# in key order, so equal contents are equal lists (Cost 2: a content can be
# named by its hash).
# Example: setting "b" to 2 in [("a", 1), ("c", 3)] gives [("a", 1), ("b", 2),
# ("c", 3)].
law AssociationList.with_entry_sets:
  for ~Value: Data
  for xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>
  for k: List<&2, U32>
  for x: Maybe<&2, Value>
  for j: List<&2, U32>
  {keys_strictly_increase(~Value, xs) == True{}: Bool}
    -> {
      keys_strictly_increase(~Value, with_entry(~Value, xs, k, x)) == True{}: Bool
    }
      & {
        value_of_first_entry_with_key(
          ~Value,
          with_entry(~Value, xs, k, x),
          j
        )
          == Bool.pick(
            Maybe<&2, Value>,
            Cmp.is_eq(WordListOrder.cmp(j, k)),
            x,
            value_of_first_entry_with_key(~Value, xs, j)
          ): Maybe<&2, Value>
      }
