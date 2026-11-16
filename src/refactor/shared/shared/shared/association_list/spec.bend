import Base
import ../shared/word_list_order/spec.bend as WordListOrder

# Lists of pairs
# --------------
# A pair is a key (a list of words) and its value.

# the value x of the key k, if it is there and the pair passes the test
def keep(
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: no code that runs calls first or ascend, so what they compute in excess costs nothing
# the value of the first pair of xs whose key is k, if any
def first(~V: Data, xs: List<&2, +Sigma<List<&2, U32>, _ => V>>, +k: List<&2, U32>) -> Maybe<&2, V>:
  match xs:
    case Nil{}:
      None{}
    case Con{(key, v), rest}:
      Bool.pick(Maybe<&2, V>, Cmp.is_eq(WordListOrder.cmp(key, k)), Some{v}, first(~V, rest, k))

# the key k comes before the key of the first pair of xs, if any
def ascend.next(~V: Data, k: List<&2, U32>, xs: List<&2, +Sigma<List<&2, U32>, _ => V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(j, w), rest}:
      Cmp.is_lt(WordListOrder.cmp(k, j))

# the keys of xs go up strictly, one pair after another
def ascend(~V: Data, xs: List<&2, +Sigma<List<&2, U32>, _ => V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{(k, v), +rest}:
      Bool.and(ascend.next(~V, k, rest), ascend(~V, rest))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the key of the last pair of xs, or k when xs is empty
def last_key(
  ~V: Data,
  xs: List<&2, +Sigma<List<&2, U32>, _ => V>>,
  k: List<&2, U32>
) -> List<&2, U32>:
  match xs:
    case Nil{}:
      k
    case Con{(j, w), rest}:
      last_key(~V, rest, j)
