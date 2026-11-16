import Base
import ../shared/shared/shared.bend as Shared

# An encoding of a type writes each value as words, and reads a value from the
# start of words, handing back the words after it. Encodings are built from five
# kinds (a word, a number, a pair, a fixed-length list, a conversion), so a type
# gets an exact encoding from the laws below, with no proof of its own.

# Exactness
# ---------

# the encodings of a family of types, one type for each index i, are exact: reading
# the encoding of a value, then any words, gives that value and those words; and
# words that read as a value and words after it are the encoding of that value,
# then those words
def ExactEncoding.On(
  ~Index: Data,
  ~A: @-i: Index -> Data,
  ~write: @i: Index -> A(i) -> List<&2, U32>,
  ~read: @i: Index -> List<&2, U32> -> Maybe<&2, +Sigma<A(i), _ => List<&2, U32>>>
) -> Type:
  @i: Index
    -> (
      (
        @a: A(
          i
        ) -> @r: List<
          &2,
          U32> -> {
          read(
            i,
            List.append(&2, U32, write(i, a), r)
          )
            == Some{(a, r)}: Maybe<&2, +Sigma<A(i), _ => List<&2, U32>>>
        }
      )
        & (
          @ws: List<
            &2,
            U32> -> @a: A(
            i
          ) -> @r: List<
            &2,
            U32> -> {
            read(i, ws) == Some{(a, r)}: Maybe<&2, +Sigma<A(i), _ => List<&2, U32>>>
          } -> {ws == List.append(&2, U32, write(i, a), r): List<&2, U32>}
        )
    )

# the encoding of A, written by write and read by read, is exact
def ExactEncoding(
  ~A: Data,
  ~write: A -> List<&2, U32>,
  ~read: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
) -> Type:
  ExactEncoding.On(~Unit, ~(u => A), ~(u => write), ~(u => read))

# A word
# ------

# the encoding of the word w
law Word.to_words:
  for w: U32
  List<&2, U32>

# the word at the start of ws, and the words after it
law Word.from_words:
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<U32, _ => List<&2, U32>>>

# Means: the encoding of a word is exact.
# For free: every encoding bottoms out in words, so every encoding built here ends in a
# encoding that is exact.
# For the goal: the words of a record, a part or a message are read back exactly
# as they were written.
# Example: the word 7, followed by 1 and 2, reads back as 7, with 1 and 2 left.
law Word.encoding_is_exact:
  ExactEncoding(~U32, ~Word.to_words, ~Word.from_words)

# A number
# --------

# the encoding of the number n
law Nat.to_words:
  for n: Nat
  List<&2, U32>

# the number at the start of ws, and the words after it
law Nat.from_words:
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>

# Means: the encoding of a natural number, of any size, is exact.
# For free: counts, lengths and tags of any size; no number wraps around, and no
# number has two encodings.
# For the goal: a list of any length, and a type of any number of
# constructors, have exact encodings.
# Example: the number 5000000000, followed by 9, reads back as 5000000000, with
# 9 left.
law Nat.encoding_is_exact:
  ExactEncoding(~Nat, ~Nat.to_words, ~Nat.from_words)

# A pair
# ------

# the encoding of the pair p: its first value, then its second, whose encoding may
# depend on the first
law DependentPair.to_words:
  for ~A: Data
  for ~B: @-x: A -> Data
  for ~write_first: A -> List<&2, U32>
  for ~write_second: @a: A -> B(a) -> List<&2, U32>
  for p: +Sigma<A, B>
  List<&2, U32>

# the pair at the start of ws, and the words after it
law DependentPair.from_words:
  for ~A: Data
  for ~B: @-x: A -> Data
  for ~read_first: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for ~read_second: @a: A -> List<&2, U32> -> Maybe<&2, +Sigma<B(a), _ => List<&2, U32>>>
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<+Sigma<A, B>, _ => List<&2, U32>>>

# Means: if the encoding of the first value is exact, and the encoding of the second
# value is exact for every first value, then the encoding of the pair is exact.
# For free: plain pairs (a second encoding that does not depend on the first);
# "one of several" (a number tag, then the value of that choice, where an
# unknown tag reads nothing); a list (its count, then that many values).
# For the goal: every record, request and message is built from pairs and
# choices, so each has an exact encoding.
# Example: the pair (2, [a, b]), where 2 says how many values follow, reads
# back as itself.
law DependentPair.encoding_is_exact:
  for ~A: Data
  for ~B: @-x: A -> Data
  for ~write_first: A -> List<&2, U32>
  for ~read_first: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for ~write_second: @a: A -> B(a) -> List<&2, U32>
  for ~read_second: @a: A -> List<&2, U32> -> Maybe<&2, +Sigma<B(a), _ => List<&2, U32>>>
  ExactEncoding(~A, ~write_first, ~read_first)
    -> ExactEncoding.On(~A, ~B, ~write_second, ~read_second)
    -> ExactEncoding(
      ~(+Sigma<A, B>),
      ~(p => DependentPair.to_words(~A, ~B, ~write_first, ~write_second, p)),
      ~(ws => DependentPair.from_words(~A, ~B, ~read_first, ~read_second, ws))
    )

# Fixed-length lists
# ---------------

# the encoding of the n values of v, one after another
law FixedLengthList.to_words:
  for ~A: Data
  for ~write_value: A -> List<&2, U32>
  for n: Nat
  for v: Shared.FixedLengthList(A, n)
  List<&2, U32>

# the n values at the start of ws, and the words after them
law FixedLengthList.from_words:
  for ~A: Data
  for ~read_value: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for n: Nat
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<Shared.FixedLengthList(A, n), _ => List<&2, U32>>>

# Means: if the encoding of a value is exact, the encoding of a fixed-length list of
# n of them is
# exact, for every n.
# For free: the value with no content (a fixed-length list of no values); with a count in
# front (a pair), lists of any length.
# For the goal: the words of a resource and the records of a message are written
# with one count, not one mark per value, so an encoding costs about the size of
# what it holds.
# Example: three words 4, 5, 6, followed by 7, read as three values give 4, 5,
# 6, with 7 left.
law FixedLengthList.encoding_is_exact:
  for ~A: Data
  for ~write_value: A -> List<&2, U32>
  for ~read_value: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  ExactEncoding(~A, ~write_value, ~read_value)
    -> ExactEncoding.On(
      ~Nat,
      ~(n => Shared.FixedLengthList(A, n)),
      ~(n => v => FixedLengthList.to_words(~A, ~write_value, n, v)),
      ~(n => ws => FixedLengthList.from_words(~A, ~read_value, n, ws))
    )

# A conversion
# ------------

# the encoding of a: the encoding of a converted to B
law Conversion.to_words:
  for ~A: Data
  for ~B: Data
  for ~convert: A -> B
  for ~write_converted: B -> List<&2, U32>
  for a: A
  List<&2, U32>

# the A at the start of ws: a B, kept when it converts back to an A
law Conversion.from_words:
  for ~A: Data
  for ~B: Data
  for ~convert_back: B -> Maybe<&2, A>
  for ~read_converted: List<&2, U32> -> Maybe<&2, +Sigma<B, _ => List<&2, U32>>>
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<A, _ => List<&2, U32>>>

# Means: if a value of A converts to B and back to the same value, and every B
# that converts back to an A is what that A converts to, then an exact encoding of
# B gives an exact encoding of A.
# For free: any Bend datatype (it converts to choices of pairs); a type with a
# rule on its values (a sorted list, a number with no leading zero), whose encoding
# reads only values that keep the rule; the type with no values (nothing
# converts back).
# For the goal: records, requests and every hook's values get exact encodings from
# the four kinds above, so no type proves its own encoding.
# Example: a Bool converts to the number 0 or 1; the words of 2 read as no Bool.
law Conversion.encoding_is_exact:
  for ~A: Data
  for ~B: Data
  for ~convert: A -> B
  for ~convert_back: B -> Maybe<&2, A>
  for ~write_converted: B -> List<&2, U32>
  for ~read_converted: List<&2, U32> -> Maybe<&2, +Sigma<B, _ => List<&2, U32>>>
  (@a: A -> {convert_back(convert(a)) == Some{a}: Maybe<&2, A>})
    -> (@b: B -> @a: A -> {convert_back(b) == Some{a}: Maybe<&2, A>} -> {convert(a) == b: B})
    -> ExactEncoding(~B, ~write_converted, ~read_converted)
    -> ExactEncoding(
      ~A,
      ~(a => Conversion.to_words(~A, ~B, ~convert, ~write_converted, a)),
      ~(ws => Conversion.from_words(~A, ~B, ~convert_back, ~read_converted, ws))
    )
