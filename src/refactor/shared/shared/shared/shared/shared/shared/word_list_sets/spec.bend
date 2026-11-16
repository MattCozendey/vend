import Base
import ../shared/word_list_order/spec.bend as WordListOrder

# a and b are the same list of words
def same(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Cmp.is_eq(WordListOrder.cmp(a, b))

# ok, and xs and ys hold the same lists of words, in the same order
def same_lists.go(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      ok
    case Con{x, rest} Con{y, more}:
      match ok:
        case False{}:
          False{}
        case True{}:
          same_lists.go(rest, more, same(x, y))
    case _ _:
      False{}

# xs and ys hold the same lists of words, in the same order
def same_lists(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  same_lists.go(xs, ys, True{})

# hit, or the list of words a is one of xs
def contains.go(xs: List<&2, List<&2, U32>>, +a: List<&2, U32>, hit: Bool) -> Bool:
  match xs:
    case Nil{}:
      hit
    case Con{x, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          contains.go(rest, a, same(x, a))

# the list of words a is one of xs
def contains(xs: List<&2, List<&2, U32>>, a: List<&2, U32>) -> Bool:
  contains.go(xs, a, False{})

# ok, and every list of words of xs is one of ys
def within.go(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{x, rest}:
      match ok:
        case False{}:
          False{}
        case True{}:
          within.go(rest, ys, contains(ys, x))

# every list of words of xs is one of ys
def within(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  within.go(xs, ys, True{})

# xs and ys hold the same lists of words, in any order and with any repeats
def same_set(+xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  within.go(xs, ys, within(ys, xs))

# the lists of xs that are not in seen, each once, in the order of xs
def dedupe.go(
  xs: List<&2, List<&2, U32>>,
  +seen: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      +known = contains(seen, x)
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, known, [], [x]),
        dedupe.go(rest, Bool.pick(List<&2, List<&2, U32>>, known, seen, x <> seen))
      )

# the lists of xs, each once, the first of each kept, in the order of xs
def dedupe(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  dedupe.go(xs, [])

# no list of words is twice in xs
def Distinct(xs: List<&2, List<&2, U32>>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, rest}:
      {contains(rest, x) == False{}: Bool} & Distinct(rest)

# Means: dedupe keeps exactly the lists of words of its input, each once.
# For free: the length of dedupe is the number of different lists; counting
# voters through dedupe never counts one voter twice.
# For the goal: a decision needs more than half of the voters, and a voter
# named twice in a group must not count twice (the old majority law allowed
# it).
# Example: dedupe of [a, b, a] is [a, b].
law dedupe_keeps_each_once:
  for xs: List<&2, List<&2, U32>>
  for a: List<&2, U32>
  {contains(dedupe(xs), a) == contains(xs, a): Bool} & Distinct(dedupe(xs))
