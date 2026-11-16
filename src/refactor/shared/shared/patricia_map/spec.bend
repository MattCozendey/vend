import Base
import ../shared.bend as Shared

# A map from keys to values that keeps, for each of its parts, a summary of the
# entries in it. A key is a list of words, ordered as Shared.Words.cmp orders
# them. The user of the map gives the type of the values (V), the type of the
# summaries (M), the measure of one entry (of), and how two summaries combine
# (combine). These four are part of the type of a map, so two maps with
# different measures can never be mixed.

# The map
# -------

# a map from keys to values of V, with a summary of each of its parts
law PatriciaMap:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  Data

# the value of the key k in m, if m has k
law PatriciaMap.get:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  for k: List<&2, U32>
  Maybe<&2, V>

# the map of the entries of xs; the first entry of a key wins
law PatriciaMap.from_list:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for xs: List<&2, +Sigma<List<&2, U32>, _ => V>>
  PatriciaMap(~V, ~M, ~of, ~combine)

# the map of the keys of a and b; both combines the two values of a key in both
law PatriciaMap.merge:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for ~both: V -> V -> V
  for a: PatriciaMap(~V, ~M, ~of, ~combine)
  for b: PatriciaMap(~V, ~M, ~of, ~combine)
  PatriciaMap(~V, ~M, ~of, ~combine)

# the entries of m that pass the test
law PatriciaMap.keep:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for ~test: List<&2, U32> -> V -> Bool
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  PatriciaMap(~V, ~M, ~of, ~combine)

# the entries of m whose keys are below s, and those whose keys are at or above s
law PatriciaMap.split:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  for s: List<&2, U32>
  PatriciaMap(~V, ~M, ~of, ~combine) & PatriciaMap(~V, ~M, ~of, ~combine)

# the entries of m
law PatriciaMap.list:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  List<&2, +Sigma<List<&2, U32>, _ => V>>

# the summary of the entries of m; nothing if m is empty
law PatriciaMap.summary:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  Maybe<&2, M>

# Laws
# ----

# Means: a map made from a list of entries holds, at each key, the value of the
# first entry with that key, and nothing at a key that no entry has.
# For free: the empty map (from the empty list) holds nothing; a map of one
# entry holds that entry only; a set is a map whose values are empty; a node can
# load its map from what it reads from disk or from another node.
# For the goal: every map starts here, so every map holds exactly what was put
# in it, and resuming a node from storage needs no other rule.
# Example: from the entries (a, 1), (b, 2), (a, 3), the value at a is 1.
law PatriciaMap.from_list_takes_first:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for xs: List<&2, +Sigma<List<&2, U32>, _ => V>>
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~V,
      ~M,
      ~of,
      ~combine,
      PatriciaMap.from_list(~V, ~M, ~of, ~combine, xs),
      k
    )
      == Shared.Pairs.first(~V, xs, k): Maybe<&2, V>
  }

# Means: a merge of two maps holds, at each key that both have, the two values
# combined by the given function; at a key that only one has, that one's value;
# at a key that neither has, nothing.
# For free: a union where the first map wins (the function keeps its first
# value); adding one entry (a merge with a map of one entry); a merge is the
# same in either order when the function is, and with a map of nothing it
# changes nothing.
# For the goal: a Sync is a merge of the facts of two nodes, so the order in
# which a node meets other nodes cannot change what it holds; hooks merge their
# own indexes with the same operation.
# Example: merging (a, 1), (b, 2) with (b, 5), (c, 3), keeping the larger
# value, gives (a, 1), (b, 5), (c, 3).
law PatriciaMap.merge_combines:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for ~both: V -> V -> V
  for a: PatriciaMap(~V, ~M, ~of, ~combine)
  for b: PatriciaMap(~V, ~M, ~of, ~combine)
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~V,
      ~M,
      ~of,
      ~combine,
      PatriciaMap.merge(~V, ~M, ~of, ~combine, ~both, a, b),
      k
    )
      == Shared.Maybe.merge(
        ~V,
        ~both,
        PatriciaMap.get(~V, ~M, ~of, ~combine, a, k),
        PatriciaMap.get(~V, ~M, ~of, ~combine, b, k)
      ): Maybe<&2, V>
  }

# Means: keeping only the entries that pass a test gives, at each key, the
# map's value if that entry passes the test, and nothing otherwise.
# For free: removing a key (keep every other key); the entries of one map that
# another map lacks; a map whose values all pass a test.
# For the goal: forgetting what a checkpoint covers is a keep, and "what the
# other node lacks" is a keep, so neither needs a rule of its own.
# Example: keeping the even values of (a, 1), (b, 2) gives (b, 2).
law PatriciaMap.keep_filters:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for ~test: List<&2, U32> -> V -> Bool
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~V,
      ~M,
      ~of,
      ~combine,
      PatriciaMap.keep(~V, ~M, ~of, ~combine, ~test, m),
      k
    )
      == Shared.Pairs.keep(~V, ~test, k, PatriciaMap.get(~V, ~M, ~of, ~combine, m, k)): Maybe<&2, V>
  }

# Means: splitting a map at a key gives two maps: the first holds the entries
# whose keys are below that key, the second those whose keys are at or above it.
# For free: the part under a key prefix and any range of keys (two splits); the
# two halves together hold the whole map, and they share no key.
# For the goal: a Sync compares two maps part by part and sends only the parts
# that differ; a hook reads a range of its index (versions 10 to 20) without
# reading the rest.
# Example: splitting (a, 1), (b, 2), (c, 3) at b gives (a, 1) and (b, 2), (c, 3).
law PatriciaMap.split_divides:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  for s: List<&2, U32>
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~V,
      ~M,
      ~of,
      ~combine,
      Pair.fst(
        PatriciaMap(~V, ~M, ~of, ~combine),
        PatriciaMap(~V, ~M, ~of, ~combine),
        PatriciaMap.split(~V, ~M, ~of, ~combine, m, s)
      ),
      k
    )
      == Shared.Maybe.when(
        ~V,
        Cmp.is_lt(Shared.Words.cmp(k, s)),
        PatriciaMap.get(~V, ~M, ~of, ~combine, m, k)
      ): Maybe<&2, V>
  }
    & {
      PatriciaMap.get(
        ~V,
        ~M,
        ~of,
        ~combine,
        Pair.snd(
          PatriciaMap(~V, ~M, ~of, ~combine),
          PatriciaMap(~V, ~M, ~of, ~combine),
          PatriciaMap.split(~V, ~M, ~of, ~combine, m, s)
        ),
        k
      )
        == Shared.Maybe.when(
          ~V,
          Cmp.is_ge(Shared.Words.cmp(k, s)),
          PatriciaMap.get(~V, ~M, ~of, ~combine, m, k)
        ): Maybe<&2, V>
    }

# Means: the list of a map holds every entry of the map exactly once, and no
# other entry, in increasing key order.
# For free: going through a map in a fixed order; the number of entries; two
# equal maps give the same list; a map made from its own list is that map.
# For the goal: hooks and a Sync go through the facts of a node with it, and
# the fixed order makes every answer built from it the same on every node.
# Example: the list of the map made from (b, 2), (a, 1) is (a, 1), (b, 2).
law PatriciaMap.list_ascends:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  {
    Shared.Pairs.ascend(~V, PatriciaMap.list(~V, ~M, ~of, ~combine, m)) == True{}: Bool
  }
    & (
      @k: List<
        &2,
        U32> -> {
        Shared.Pairs.first(
          ~V,
          PatriciaMap.list(~V, ~M, ~of, ~combine, m),
          k
        )
          == PatriciaMap.get(~V, ~M, ~of, ~combine, m, k): Maybe<&2, V>
      }
    )

# Means: when combining summaries is associative, the summary of a map is the
# measures of its entries combined in list order, and the summary of an empty
# map is nothing.
# For free: the summary of a part is the two halves' summaries combined; any
# count, total or hash of the entries, chosen by the user, kept ready at every
# part.
# For the goal: two nodes find where their maps differ by comparing summaries
# of parts, so a Sync costs what differs, not what the nodes hold; a summary
# that never changes cannot pass this law.
# Example: with the measure "1" and the combine "add", the summary of a map of
# 3 entries is 3.
law PatriciaMap.summary_folds:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for m: PatriciaMap(~V, ~M, ~of, ~combine)
  (@a: M -> @b: M -> @c: M -> {combine(combine(a, b), c) == combine(a, combine(b, c)): M})
    -> {
      PatriciaMap.summary(
        ~V,
        ~M,
        ~of,
        ~combine,
        m
      )
        == Shared.Pairs.fold(
          ~V,
          ~M,
          ~of,
          ~combine,
          PatriciaMap.list(~V, ~M, ~of, ~combine, m)
        ): Maybe<&2, M>
    }

# Means: two maps that hold the same value at every key are the same map.
# For free: every function of a map gives the same result for two maps with the
# same entries; a merge, a keep or a split gives the same map however the
# entries got there; the union is commutative, associative and idempotent.
# For the goal: two nodes that hold the same facts are in the same state,
# whatever order they got the facts in, so they give the same answers.
# Example: adding a then b gives the same map as adding b then a.
law PatriciaMap.same_values_same_map:
  for ~V: Data
  for ~M: Data
  for ~of: List<&2, U32> -> V -> M
  for ~combine: M -> M -> M
  for a: PatriciaMap(~V, ~M, ~of, ~combine)
  for b: PatriciaMap(~V, ~M, ~of, ~combine)
  (
    @k: List<
      &2,
      U32> -> {
      PatriciaMap.get(
        ~V,
        ~M,
        ~of,
        ~combine,
        a,
        k
      )
        == PatriciaMap.get(~V, ~M, ~of, ~combine, b, k): Maybe<&2, V>
    }
  ) -> {a == b: PatriciaMap(~V, ~M, ~of, ~combine)}
