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
