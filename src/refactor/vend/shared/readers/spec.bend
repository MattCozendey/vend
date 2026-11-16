import Base
import ../../../shared/shared/shared/shared/shared/shared/item_merge/spec.bend as ItemMerge
import ../../../shared/shared/shared/shared/shared/shared/shared/word_list_order/spec.bend as WordListOrder

# Readers: how the content of a resource is read. A resource is anything with
# an address, not only a file, and its content is its bytes, one per word. A
# resource is bound to a reader by name, never by a file name. A reader is any
# pure function of the content: it may decode, follow closures, or interpret a
# language as deeply as it needs, as long as it has no effects (it never runs
# the resource against the world). Its reading gives the items of the content
# (lines, functions, blocks; a reader may hand a nested part to another reader
# and splice in that reader's items, at any depth) and what the resource
# depends on, each dependency under the build conditions in which it holds,
# aliases already resolved. A resource with no reader of ours is a byte
# stream: one whole item, no dependency.

# a build condition: always, a flag that the build sets, or not, and or or of
# conditions
type Condition is Data:
  ConditionAlways{}
  ConditionFlag{name: List<&2, U32>}
  ConditionNot{inner: Condition}
  ConditionAnd{left: Condition, right: Condition}
  ConditionOr{left: Condition, right: Condition}

# what a resource depends on: the address of the target, and the condition
# under which the dependency holds
type Dependency is Data:
  Dependency{target: List<&2, U32>, condition: Condition}

# a reading of a content: its items, in order, and its dependencies
type Reading is Data:
  Reading{items: List<&2, List<&2, U32>>, dependencies: List<&2, Dependency>}

# found, or the flag f is one of fs
def has_flag.go(fs: List<&2, List<&2, U32>>, +f: List<&2, U32>, found: Bool) -> Bool:
  match fs:
    case Nil{}:
      found
    case Con{x, rest}:
      match found:
        case True{}:
          True{}
        case False{}:
          has_flag.go(rest, f, Cmp.is_eq(WordListOrder.cmp(x, f)))

# the flag f is one of fs
def has_flag(fs: List<&2, List<&2, U32>>, f: List<&2, U32>) -> Bool:
  has_flag.go(fs, f, False{})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a condition is a small tree written in a resource: judging both sides of an and or an or costs at most its size
# the condition c holds in the build of the flags fs
def Condition.holds(c: Condition, +fs: List<&2, List<&2, U32>>) -> Bool:
  match c:
    case ConditionAlways{}:
      True{}
    case ConditionFlag{f}:
      has_flag(fs, f)
    case ConditionNot{x}:
      Bool.not(Condition.holds(x, fs))
    case ConditionAnd{a, b}:
      Bool.and(Condition.holds(a, fs), Condition.holds(b, fs))
    case ConditionOr{a, b}:
      Bool.or(Condition.holds(a, fs), Condition.holds(b, fs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the items of the reading r
def Reading.items(r: Reading) -> List<&2, List<&2, U32>>:
  match r:
    case Reading{xs, ds}:
      xs

# the targets of the dependencies ds that hold in the build of the flags fs
def Dependencies.in_build(
  ds: List<&2, Dependency>,
  +fs: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      []
    case Con{Dependency{t, c}, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, Condition.holds(c, fs), [t], []),
        Dependencies.in_build(rest, fs)
      )

# what the resource read as r depends on, directly, in the build of the flags fs
def Reading.depends_on(r: Reading, fs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match r:
    case Reading{xs, ds}:
      Dependencies.in_build(ds, fs)

# Built-in readers
# ----------------

# the reading of a byte stream: the whole content as one item, no dependency
def Readers.whole(c: List<&2, U32>) -> Reading:
  Reading{[c], []}

# the lines of c, after the line so far (in reverse): each line ends with its
# newline byte (10), and the last one may have none
def Readers.lines.go(c: List<&2, U32>, +line: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match c:
    case Nil{}:
      match line:
        case Nil{}:
          []
        case Con{x, rest}:
          [List.reverse(&2, U32, line)]
    case Con{+b, rest}:
      +ended = U32.is_eq(b, 10)
      +grown = {b <> line: List<&2, U32>}
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, ended, [List.reverse(&2, U32, grown)], []),
        Readers.lines.go(rest, Bool.pick(List<&2, U32>, ended, [], grown))
      )

# the reading of text in no language of ours: its lines, no dependency
def Readers.lines(c: List<&2, U32>) -> Reading:
  Reading{Readers.lines.go(c, []), []}

# Merging
# -------

# the items xs, joined
def joined(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  List.concat(&2, U32, xs)

# the merge of the contents base, ours and theirs, read by the reader of the
# name reader through read; none inside: the resource is absent; None outside:
# they clash
law Readers.merge:
  for ~read: List<&2, U32> -> List<&2, U32> -> Reading
  for reader: List<&2, U32>
  for base: Maybe<&2, List<&2, U32>>
  for ours: Maybe<&2, List<&2, U32>>
  for theirs: Maybe<&2, List<&2, U32>>
  Maybe<&2, Maybe<&2, List<&2, U32>>>

# read never loses content: the items of any reading, joined, are the content
def ReadsLosslessly(~read: List<&2, U32> -> List<&2, U32> -> Reading) -> Type:
  @reader: List<
    &2,
    U32> -> @c: List<&2, U32> -> {joined(Reading.items(read(reader, c))) == c: List<&2, U32>}

# the merge m of items, joined, if there is one
def merged(m: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{Some{joined(xs)}}

# Laws
# ----

# Means: the built-in readers lose nothing: the items of the whole reading and
# of the lines reading, joined, are the content.
# For free: a byte stream and a text in no language of ours are kept and merged
# without changing a byte; their merges are the items merged and joined.
# For the goal: lines for unknown text, one whole part otherwise (Resource),
# and nothing is lost by reading.
# Example: the lines of "a\nb" are "a\n" and "b", and joined they are "a\nb".
law Readers.built_in_lose_nothing:
  for c: List<&2, U32>
  {
    joined(Reading.items(Readers.whole(c))) == c: List<&2, U32>
  }
    & {joined(Reading.items(Readers.lines(c))) == c: List<&2, U32>}

# Means: when base, ours and theirs are all present, the merge is the item
# merge of their readings' items, joined, or a clash when the item merge
# clashes.
# For free: with a reader that loses nothing, item merge's laws hold of
# resources: a change made on only one side is never lost; ours unchanged gives
# theirs; both making one change gives that change; two changes clash only when
# they touch the same items.
# For the goal: merges go resource by resource, each in its own reader
# (Branch, Resource), and a merge never loses a change made on only one side.
# Example: base "a\nb\n", ours "x\nb\n", theirs "a\ny\n", read as lines,
# merge to "x\ny\n".
law Readers.merge_present:
  for ~read: List<&2, U32> -> List<&2, U32> -> Reading
  for reader: List<&2, U32>
  for base: List<&2, U32>
  for ours: List<&2, U32>
  for theirs: List<&2, U32>
  {
    Readers.merge(
      ~read,
      reader,
      Some{base},
      Some{ours},
      Some{theirs}
    )
      == merged(
        ItemMerge.ItemMerge.merge(
          Reading.items(read(reader, base)),
          Reading.items(read(reader, ours)),
          Reading.items(read(reader, theirs))
        )
      ): Maybe<&2, Maybe<&2, List<&2, U32>>>
  }

# Means: when base, ours or theirs is absent (the resource was added or
# deleted), the merge is theirs when ours did not change, ours when theirs did
# not change or both are the same, and a clash otherwise.
# For free: a deletion on one side and no change on the other deletes; two
# different additions of one address clash; a deletion against a change
# clashes, so neither is lost silently.
# For the goal: a merge never loses a change made on only one side (Resource),
# and a conflict is stored and shared (Branch).
# Example: base absent, ours "a", theirs absent: the merge is "a".
law Readers.merge_absent:
  for ~read: List<&2, U32> -> List<&2, U32> -> Reading
  for reader: List<&2, U32>
  for base: Maybe<&2, List<&2, U32>>
  for ours: Maybe<&2, List<&2, U32>>
  for theirs: Maybe<&2, List<&2, U32>>
  {
    Bool.and(
      Maybe.is_some(&2, List<&2, U32>, base),
      Bool.and(Maybe.is_some(&2, List<&2, U32>, ours), Maybe.is_some(&2, List<&2, U32>, theirs))
    )
      == False{}: Bool
  }
    -> (
      (
        {
          ours == base: Maybe<&2, List<&2, U32>>
        } -> {
          Readers.merge(
            ~read,
            reader,
            base,
            ours,
            theirs
          )
            == Some{theirs}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
      )
        & (
          (
            {
              theirs == base: Maybe<&2, List<&2, U32>>
            } -> {
              Readers.merge(
                ~read,
                reader,
                base,
                ours,
                theirs
              )
                == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>
            }
          )
            & (
              (
                {
                  ours == theirs: Maybe<&2, List<&2, U32>>
                } -> {
                  Readers.merge(
                    ~read,
                    reader,
                    base,
                    ours,
                    theirs
                  )
                    == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>
                }
              )
                & (
                  (
                    {ours == base: Maybe<&2, List<&2, U32>>} -> Empty
                  ) -> (
                    {theirs == base: Maybe<&2, List<&2, U32>>} -> Empty
                  ) -> (
                    {ours == theirs: Maybe<&2, List<&2, U32>>} -> Empty
                  ) -> {
                    Readers.merge(
                      ~read,
                      reader,
                      base,
                      ours,
                      theirs
                    )
                      == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>
                  }
                )
            )
        )
    )
