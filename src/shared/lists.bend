import Base

# dropping nothing keeps a list
def List.drop_zero(a, -A: Kind(a), xs: List<a, A>) -> {List.drop(a, A, xs, 0n) == xs: List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# appending nothing keeps a list
def List.append_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, []) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %List.append_nil(A, t): {h <> List.append(&2, A, t, []) == h <> _: List<&2, A>}
      {==}

# dropping the first list of an append leaves the second
def List.drop_after_append(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>
) -> {List.drop(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == ys: List<&2, A>}:
  match xs:
    case Nil{}:
      List.drop_zero(&2, A, ys)
    case Con{h, t}:
      List.drop_after_append(A, t, ys)

# a filter.put commutes with an append after it
def List.filter.put_append(
  -A: Data,
  x: A,
  a: List<&2, A>,
  b: List<&2, A>,
  hit: Bool
) -> {
  List.filter.put(
    A,
    x,
    List.append(&2, A, a, b),
    hit
  )
    == List.append(&2, A, List.filter.put(A, x, a, hit), b): List<&2, A>
}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# a pair is its two parts
def Pair.eta(-A: Data, -B: Data, p: A & B) -> {(Pair.fst(A, B, p), Pair.snd(A, B, p)) == p: A & B}:
  match p:
    case (x, y):
      {==}
