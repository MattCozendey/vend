import Base
import ../shared/shared.bend as Shared

# An encoding of a type writes each value as words, and reads a value from the
# start of words, handing back the words after it. Encodings are built from five
# kinds (a word, a number, a pair, n values in a row, a conversion), so a type
# gets an exact encoding from the laws below, with no proof of its own.

# Exactness
# ---------

# the encodings of a family of types, one type for each index i, are exact: reading
# the encoding of a value, then any words, gives that value and those words; and
# words that read as a value and words after it are the encoding of that value,
# then those words
def ExactEncoding.On(
  ~I: Data,
  ~A: @-i: I -> Data,
  ~write: @i: I -> A(i) -> List<&2, U32>,
  ~read: @i: I -> List<&2, U32> -> Maybe<&2, +Sigma<A(i), _ => List<&2, U32>>>
) -> Type:
  @i: I
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
# For the goal: the words of a fact, a part or a message are read back exactly
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
  for ~wa: A -> List<&2, U32>
  for ~wb: @a: A -> B(a) -> List<&2, U32>
  for p: +Sigma<A, B>
  List<&2, U32>

# the pair at the start of ws, and the words after it
law DependentPair.from_words:
  for ~A: Data
  for ~B: @-x: A -> Data
  for ~ra: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for ~rb: @a: A -> List<&2, U32> -> Maybe<&2, +Sigma<B(a), _ => List<&2, U32>>>
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<+Sigma<A, B>, _ => List<&2, U32>>>

# Means: if the encoding of the first value is exact, and the encoding of the second
# value is exact for every first value, then the encoding of the pair is exact.
# For free: plain pairs (a second encoding that does not depend on the first);
# "one of several" (a number tag, then the value of that choice, where an
# unknown tag reads nothing); a list (its count, then that many values).
# For the goal: every fact, request and message is built from pairs and
# choices, so each has an exact encoding.
# Example: the pair (2, [a, b]), where 2 says how many values follow, reads
# back as itself.
law DependentPair.encoding_is_exact:
  for ~A: Data
  for ~B: @-x: A -> Data
  for ~wa: A -> List<&2, U32>
  for ~ra: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for ~wb: @a: A -> B(a) -> List<&2, U32>
  for ~rb: @a: A -> List<&2, U32> -> Maybe<&2, +Sigma<B(a), _ => List<&2, U32>>>
  ExactEncoding(~A, ~wa, ~ra)
    -> ExactEncoding.On(~A, ~B, ~wb, ~rb)
    -> ExactEncoding(
      ~(+Sigma<A, B>),
      ~(p => DependentPair.to_words(~A, ~B, ~wa, ~wb, p)),
      ~(ws => DependentPair.from_words(~A, ~B, ~ra, ~rb, ws))
    )

# Values in a row
# ---------------

# the encoding of the n values of v, one after another
law Row.to_words:
  for ~A: Data
  for ~wa: A -> List<&2, U32>
  for n: Nat
  for v: Shared.Row(A, n)
  List<&2, U32>

# the n values at the start of ws, and the words after them
law Row.from_words:
  for ~A: Data
  for ~ra: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  for n: Nat
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<Shared.Row(A, n), _ => List<&2, U32>>>

# Means: if the encoding of a value is exact, the encoding of n values in a row is
# exact, for every n.
# For free: the value with no content (no values in a row); with a count in
# front (a pair), lists of any length.
# For the goal: the words of a resource and the facts of a message are written
# with one count, not one mark per value, so an encoding costs about the size of
# what it holds.
# Example: three words 4, 5, 6, followed by 7, read as three values give 4, 5,
# 6, with 7 left.
law Row.encoding_is_exact:
  for ~A: Data
  for ~wa: A -> List<&2, U32>
  for ~ra: List<&2, U32> -> Maybe<&2, +Sigma<A, _ => List<&2, U32>>>
  ExactEncoding(~A, ~wa, ~ra)
    -> ExactEncoding.On(
      ~Nat,
      ~(n => Shared.Row(A, n)),
      ~(n => v => Row.to_words(~A, ~wa, n, v)),
      ~(n => ws => Row.from_words(~A, ~ra, n, ws))
    )

# A conversion
# ------------

# the encoding of a: the encoding of a converted to B
law Conversion.to_words:
  for ~A: Data
  for ~B: Data
  for ~to: A -> B
  for ~wb: B -> List<&2, U32>
  for a: A
  List<&2, U32>

# the A at the start of ws: a B, kept when it converts back to an A
law Conversion.from_words:
  for ~A: Data
  for ~B: Data
  for ~from: B -> Maybe<&2, A>
  for ~rb: List<&2, U32> -> Maybe<&2, +Sigma<B, _ => List<&2, U32>>>
  for ws: List<&2, U32>
  Maybe<&2, +Sigma<A, _ => List<&2, U32>>>

# Means: if a value of A converts to B and back to the same value, and every B
# that converts back to an A is what that A converts to, then an exact encoding of
# B gives an exact encoding of A.
# For free: any Bend datatype (it converts to choices of pairs); a type with a
# rule on its values (a sorted list, a number with no leading zero), whose encoding
# reads only values that keep the rule; the type with no values (nothing
# converts back).
# For the goal: facts, requests and every hook's values get exact encodings from
# the four kinds above, so no type proves its own encoding.
# Example: a Bool converts to the number 0 or 1; the words of 2 read as no Bool.
law Conversion.encoding_is_exact:
  for ~A: Data
  for ~B: Data
  for ~to: A -> B
  for ~from: B -> Maybe<&2, A>
  for ~wb: B -> List<&2, U32>
  for ~rb: List<&2, U32> -> Maybe<&2, +Sigma<B, _ => List<&2, U32>>>
  (@a: A -> {from(to(a)) == Some{a}: Maybe<&2, A>})
    -> (@b: B -> @a: A -> {from(b) == Some{a}: Maybe<&2, A>} -> {to(a) == b: B})
    -> ExactEncoding(~B, ~wb, ~rb)
    -> ExactEncoding(
      ~A,
      ~(a => Conversion.to_words(~A, ~B, ~to, ~wb, a)),
      ~(ws => Conversion.from_words(~A, ~B, ~from, ~rb, ws))
    )
