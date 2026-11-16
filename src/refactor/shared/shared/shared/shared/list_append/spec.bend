import Base

# Laws of Base's List.append, the join of two lists. Base states none.

# Means: joining a and b, then c, gives the same list as joining a with the
# join of b and c.
# For free: a list joined from many pieces is the same however the joins are
# grouped.
# For the goal: an encoding is joined from the encodings of its parts, and the
# proofs that encodings are exact regroup those joins.
# Example: [1] joined with [2, 3], then with [4], is [1] joined with [2, 3, 4].
law List.append_is_associative:
  for -A: Data
  for a: List<&2, A>
  for b: List<&2, A>
  for c: List<&2, A>
  {
    List.append(
      &2,
      A,
      List.append(&2, A, a, b),
      c
    )
      == List.append(&2, A, a, List.append(&2, A, b, c)): List<&2, A>
  }

# Means: joining a list with the empty list, on either side, gives that list.
# For free: an empty encoding (no values in a row) adds nothing to the words
# around it.
# For the goal: the encodings of the value with no content and of an empty row
# are empty, and the proofs drop them with this law.
# Example: [] joined with [1, 2] is [1, 2], and so is [1, 2] joined with [].
law List.append_empty_changes_nothing:
  for -A: Data
  for a: List<&2, A>
  {List.append(&2, A, [], a) == a: List<&2, A>} & {List.append(&2, A, a, []) == a: List<&2, A>}
