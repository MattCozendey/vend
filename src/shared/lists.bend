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
