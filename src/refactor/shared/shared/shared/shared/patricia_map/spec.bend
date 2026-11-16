import Base
import ../shared/association_list/spec.bend as AssociationList
import ../shared/shared/shared.bend as Shared
import ../shared/shared/word_list_order/spec.bend as WordListOrder

# A map from keys to values that keeps, for each of its parts, a summary of the
# entries in it. A key is a list of words, ordered as WordListOrder.cmp orders
# them. The user of the map gives the type of the values (Value), the type of
# the summaries (Summary), the summary of one entry (measure_entry), and how two
# summaries combine (combine_summaries). These four are part of the type of a
# map, so two maps with different measures can never be mixed.

# The map
# -------

# a map from keys to values of Value, with a summary of each of its parts
law PatriciaMap:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  Data

# the value of the key k in m, if m has k
law PatriciaMap.get:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for k: List<&2, U32>
  Maybe<&2, Value>

# the map of the entries of xs; the first entry of a key wins
law PatriciaMap.from_list:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>
  PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)

# the map of the keys of a and b; both combines the two values of a key in both
law PatriciaMap.merge:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for ~combine_values: Value -> Value -> Value
  for a: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for b: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)

# the entries of m that pass the test
law PatriciaMap.keep:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for ~keeps_entry: List<&2, U32> -> Value -> Bool
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)

# the entries of m whose keys are below s, and those whose keys are at or above s
law PatriciaMap.split:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for s: List<&2, U32>
  PatriciaMap(
    ~Value,
    ~Summary,
    ~measure_entry,
    ~combine_summaries
  )
    & PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)

# the entries of m
law PatriciaMap.list:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  List<&2, +Sigma<List<&2, U32>, _ => Value>>

# the summary of the entries of m; nothing if m is empty
law PatriciaMap.summary:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  Maybe<&2, Summary>

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
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for xs: List<&2, +Sigma<List<&2, U32>, _ => Value>>
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~Value,
      ~Summary,
      ~measure_entry,
      ~combine_summaries,
      PatriciaMap.from_list(~Value, ~Summary, ~measure_entry, ~combine_summaries, xs),
      k
    )
      == AssociationList.value_of_first_entry_with_key(~Value, xs, k): Maybe<&2, Value>
  }

# Means: a merge of two maps holds, at each key that both have, the two values
# combined by the given function; at a key that only one has, that one's value;
# at a key that neither has, nothing.
# For free: a union where the first map wins (the function keeps its first
# value); adding one entry (a merge with a map of one entry); a merge is the
# same in either order when the function is, and with a map of nothing it
# changes nothing.
# For the goal: a Sync is a merge of the records of two nodes, so the order in
# which a node meets other nodes cannot change what it holds; hooks merge their
# own indexes with the same operation.
# Example: merging (a, 1), (b, 2) with (b, 5), (c, 3), keeping the larger
# value, gives (a, 1), (b, 5), (c, 3).
law PatriciaMap.merge_combines:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for ~combine_values: Value -> Value -> Value
  for a: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for b: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~Value,
      ~Summary,
      ~measure_entry,
      ~combine_summaries,
      PatriciaMap.merge(
        ~Value,
        ~Summary,
        ~measure_entry,
        ~combine_summaries,
        ~combine_values,
        a,
        b
      ),
      k
    )
      == Shared.Maybe.merge(
        ~Value,
        ~combine_values,
        PatriciaMap.get(~Value, ~Summary, ~measure_entry, ~combine_summaries, a, k),
        PatriciaMap.get(~Value, ~Summary, ~measure_entry, ~combine_summaries, b, k)
      ): Maybe<&2, Value>
  }

# Means: keeping only the entries that pass a test gives, at each key, the
# map's value if that entry passes the test, and nothing otherwise.
# For free: removing a key (keep every other key); the entries of one map that
# another map lacks; a map whose values all pass a test.
# For the goal: forgetting what a checkpoint covers is a keep, and "what the
# other node lacks" is a keep, so neither needs a rule of its own.
# Example: keeping the even values of (a, 1), (b, 2) gives (b, 2).
law PatriciaMap.keep_filters:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for ~keeps_entry: List<&2, U32> -> Value -> Bool
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~Value,
      ~Summary,
      ~measure_entry,
      ~combine_summaries,
      PatriciaMap.keep(~Value, ~Summary, ~measure_entry, ~combine_summaries, ~keeps_entry, m),
      k
    )
      == AssociationList.value_if_entry_passes(
        ~Value,
        ~keeps_entry,
        k,
        PatriciaMap.get(~Value, ~Summary, ~measure_entry, ~combine_summaries, m, k)
      ): Maybe<&2, Value>
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
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for s: List<&2, U32>
  for k: List<&2, U32>
  {
    PatriciaMap.get(
      ~Value,
      ~Summary,
      ~measure_entry,
      ~combine_summaries,
      Pair.fst(
        PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
        PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
        PatriciaMap.split(~Value, ~Summary, ~measure_entry, ~combine_summaries, m, s)
      ),
      k
    )
      == Shared.Maybe.when(
        ~Value,
        Cmp.is_lt(WordListOrder.cmp(k, s)),
        PatriciaMap.get(~Value, ~Summary, ~measure_entry, ~combine_summaries, m, k)
      ): Maybe<&2, Value>
  }
    & {
      PatriciaMap.get(
        ~Value,
        ~Summary,
        ~measure_entry,
        ~combine_summaries,
        Pair.snd(
          PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
          PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
          PatriciaMap.split(~Value, ~Summary, ~measure_entry, ~combine_summaries, m, s)
        ),
        k
      )
        == Shared.Maybe.when(
          ~Value,
          Cmp.is_ge(WordListOrder.cmp(k, s)),
          PatriciaMap.get(~Value, ~Summary, ~measure_entry, ~combine_summaries, m, k)
        ): Maybe<&2, Value>
    }

# Means: the list of a map holds every entry of the map exactly once, and no
# other entry, in increasing key order.
# For free: going through a map in a fixed order; the number of entries; two
# equal maps give the same list; a map made from its own list is that map.
# For the goal: hooks and a Sync go through the records of a node with it, and
# the fixed order makes every answer built from it the same on every node.
# Example: the list of the map made from (b, 2), (a, 1) is (a, 1), (b, 2).
law PatriciaMap.list_ascends:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  {
    AssociationList.keys_strictly_increase(
      ~Value,
      PatriciaMap.list(~Value, ~Summary, ~measure_entry, ~combine_summaries, m)
    )
      == True{}: Bool
  }
    & (
      @k: List<
        &2,
        U32> -> {
        AssociationList.value_of_first_entry_with_key(
          ~Value,
          PatriciaMap.list(~Value, ~Summary, ~measure_entry, ~combine_summaries, m),
          k
        )
          == PatriciaMap.get(
            ~Value,
            ~Summary,
            ~measure_entry,
            ~combine_summaries,
            m,
            k
          ): Maybe<&2, Value>
      }
    )

# Means: the summary of an empty map is nothing; of a map with one entry, the
# measure of that entry; of a map with more entries, the summaries of its two
# halves combined, where the halves are split at the first bit where the keys of
# its first and last entries differ (WordListOrder.split_key).
# For free: the summary of every part under a key prefix is ready, and it is
# the same on every map that has the same entries in that part; with a combine
# that is associative (a count, a sum), the summary is the measures combined in
# list order; with "hash of the two summaries" as the combine, the summary is a
# Merkle hash, so two different parts share a summary only when SHA-256 has a
# collision.
# For the goal: a Sync compares two maps part by part, from the top, and sends
# only the parts whose summaries differ, so it costs what differs, and it
# trusts nothing but SHA-256 (Trust 1).
# Example: with the measure "1" and the combine "add", the summary of a map of
# 3 entries is 3.
law PatriciaMap.summary_splits:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for m: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  (
    {
      PatriciaMap.list(
        ~Value,
        ~Summary,
        ~measure_entry,
        ~combine_summaries,
        m
      )
        == []: List<&2, +Sigma<List<&2, U32>, _ => Value>>
    } -> {
      PatriciaMap.summary(
        ~Value,
        ~Summary,
        ~measure_entry,
        ~combine_summaries,
        m
      )
        == None{}: Maybe<&2, Summary>
    }
  )
    & (
      @k: List<
        &2,
        U32> -> @v: Value -> {
        PatriciaMap.list(
          ~Value,
          ~Summary,
          ~measure_entry,
          ~combine_summaries,
          m
        )
          == [(k, v)]: List<&2, +Sigma<List<&2, U32>, _ => Value>>
      } -> {
        PatriciaMap.summary(
          ~Value,
          ~Summary,
          ~measure_entry,
          ~combine_summaries,
          m
        )
          == Some{measure_entry(k, v)}: Maybe<&2, Summary>
      }
    )
    & (
      @k: List<
        &2,
        U32> -> @v: Value -> @j: List<
        &2,
        U32> -> @w: Value -> @more: List<
        &2,
        +Sigma<
          List<&2, U32>,
          _ => Value>> -> {
        PatriciaMap.list(
          ~Value,
          ~Summary,
          ~measure_entry,
          ~combine_summaries,
          m
        )
          == (k, v)
          <> (j, w)
          <> more: List<&2, +Sigma<List<&2, U32>, _ => Value>>
      } -> {
        PatriciaMap.summary(
          ~Value,
          ~Summary,
          ~measure_entry,
          ~combine_summaries,
          m
        )
          == Shared.Maybe.merge(
            ~Summary,
            ~combine_summaries,
            PatriciaMap.summary(
              ~Value,
              ~Summary,
              ~measure_entry,
              ~combine_summaries,
              Pair.fst(
                PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
                PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
                PatriciaMap.split(
                  ~Value,
                  ~Summary,
                  ~measure_entry,
                  ~combine_summaries,
                  m,
                  WordListOrder.split_key(k, AssociationList.key_of_last_entry(~Value, more, j))
                )
              )
            ),
            PatriciaMap.summary(
              ~Value,
              ~Summary,
              ~measure_entry,
              ~combine_summaries,
              Pair.snd(
                PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
                PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries),
                PatriciaMap.split(
                  ~Value,
                  ~Summary,
                  ~measure_entry,
                  ~combine_summaries,
                  m,
                  WordListOrder.split_key(k, AssociationList.key_of_last_entry(~Value, more, j))
                )
              )
            )
          ): Maybe<&2, Summary>
      }
    )

# Means: two maps that hold the same value at every key are the same map.
# For free: every function of a map gives the same result for two maps with the
# same entries; a merge, a keep or a split gives the same map however the
# entries got there; the union is commutative, associative and idempotent.
# For the goal: two nodes that hold the same records are in the same state,
# whatever order they got the records in, so they give the same answers.
# Example: adding a then b gives the same map as adding b then a.
law PatriciaMap.same_values_same_map:
  for ~Value: Data
  for ~Summary: Data
  for ~measure_entry: List<&2, U32> -> Value -> Summary
  for ~combine_summaries: Summary -> Summary -> Summary
  for a: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  for b: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)
  (
    @k: List<
      &2,
      U32> -> {
      PatriciaMap.get(
        ~Value,
        ~Summary,
        ~measure_entry,
        ~combine_summaries,
        a,
        k
      )
        == PatriciaMap.get(
          ~Value,
          ~Summary,
          ~measure_entry,
          ~combine_summaries,
          b,
          k
        ): Maybe<&2, Value>
    }
  ) -> {a == b: PatriciaMap(~Value, ~Summary, ~measure_entry, ~combine_summaries)}
