import Base
import ../shared/word_list_order/spec.bend as WordListOrder

# Item merge: three-way merge of lists of items (an item is a list of words: a
# line, a function, a block). A diff is an edit script over the base: each
# base item is kept or removed, and items are inserted between them. A merge
# takes the diffs from the base to each side; when their changes are apart, it
# applies both; when they touch or overlap and differ, it clashes. So a merge
# never loses a change made on only one side.

# what an edit script does at one point of the base
type ItemEdit is Data:
  ItemKept{}
  ItemRemoved{}
  ItemInserted{item: List<&2, U32>}

# a run of changes of an edit script: from the base item at start, removed
# base items are removed, and the items inserted are put in their place
type Hunk is Data:
  Hunk{start: Nat, removed: Nat, inserted: List<&2, List<&2, U32>>}

# the items a and b are the same
def same_item(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Cmp.is_eq(WordListOrder.cmp(a, b))

# the item x in front of the items m, if there are any
def cons_some(
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, List<&2, U32>>>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# the items a after the edit script es: None when es does not fit a (it keeps
# or removes more items than a has, or fewer)
def apply(es: List<&2, ItemEdit>, a: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match es:
    case Nil{}:
      match a:
        case Nil{}:
          Some{[]}
        case Con{x, ta}:
          None{}
    case Con{e, rest}:
      match e:
        case ItemInserted{y}:
          cons_some(y, apply(rest, a))
        case ItemKept{}:
          match a:
            case Nil{}:
              None{}
            case Con{x, ta}:
              cons_some(x, apply(rest, ta))
        case ItemRemoved{}:
          match a:
            case Nil{}:
              None{}
            case Con{x, ta}:
              apply(rest, ta)

# how many base items the edit script es keeps
def kept(es: List<&2, ItemEdit>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      match e:
        case ItemKept{}:
          1n+kept(rest)
        case _:
          kept(rest)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: lcs_length states what a diff keeps, and no code that runs calls it
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- said only in laws: no code that runs calls lcs_length, so running its calls in parallel gains nothing
# the length of a longest list of items that a and b both hold in order
def lcs_length(a: List<&2, List<&2, U32>>, +b: List<&2, List<&2, U32>>) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{+x, +ta}:
      match b:
        case Nil{}:
          0n
        case Con{+y, +tb}:
          Bool.pick(
            Nat,
            same_item(x, y),
            1n+lcs_length(ta, tb),
            Nat.max(lcs_length(ta, b), lcs_length(x <> ta, tb))
          )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the hunk that starts at start, if it changes anything; inserted holds its
# inserted items in reverse
def hunk_of(start: Nat, removed: Nat, inserted: List<&2, List<&2, U32>>) -> List<&2, Hunk>:
  match removed inserted:
    case 0n Nil{}:
      []
    case r xs:
      [Hunk{start, r, List.reverse(&2, List<&2, U32>, xs)}]

# the hunks of the edit script es, from base position i, with the hunk that
# started at start, with removed items removed and the items inserted so far
# (in reverse)
def hunks.go(
  es: List<&2, ItemEdit>,
  +i: Nat,
  start: Nat,
  removed: Nat,
  inserted: List<&2, List<&2, U32>>
) -> List<&2, Hunk>:
  match es:
    case Nil{}:
      hunk_of(start, removed, inserted)
    case Con{e, rest}:
      match e:
        case ItemKept{}:
          List.append(
            &2,
            Hunk,
            hunk_of(start, removed, inserted),
            hunks.go(rest, 1n+i, 1n+i, 0n, [])
          )
        case ItemRemoved{}:
          hunks.go(rest, 1n+i, start, 1n+removed, inserted)
        case ItemInserted{y}:
          hunks.go(rest, i, start, removed, y <> inserted)

# the hunks of the edit script es
def hunks(es: List<&2, ItemEdit>) -> List<&2, Hunk>:
  hunks.go(es, 0n, 0n, 0n, [])

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: these helpers say when two changes clash, and no code that runs calls them
# the items xs and ys are the same, one for one
def same_items(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, rx} Con{y, ry}:
      Bool.and(same_item(x, y), same_items(rx, ry))
    case _ _:
      False{}

# the hunks a and b are the same
def same_hunk(a: Hunk, b: Hunk) -> Bool:
  match a b:
    case Hunk{sa, ra, xa} Hunk{sb, rb, xb}:
      Bool.and(Bool.and(Nat.is_eq(sa, sb), Nat.is_eq(ra, rb)), same_items(xa, xb))

# the hunks a and b touch or overlap: each starts at or before the other ends
def touch(a: Hunk, b: Hunk) -> Bool:
  match a b:
    case Hunk{+sa, ra, xa} Hunk{+sb, rb, xb}:
      Bool.and(Nat.is_le(sa, Nat.add(sb, rb)), Nat.is_le(sb, Nat.add(sa, ra)))

# the hunk a clashes with a hunk of bs: they touch or overlap and differ
def clashes_with(+a: Hunk, bs: List<&2, Hunk>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{+b, rest}:
      Bool.or(Bool.and(touch(a, b), Bool.not(same_hunk(a, b))), clashes_with(a, rest))

# a hunk of as clashes with a hunk of bs
def clash(as: List<&2, Hunk>, +bs: List<&2, Hunk>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{a, rest}:
      Bool.or(clashes_with(a, bs), clash(rest, bs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the edit e in front of the script m, if there is one
def edit_some(e: ItemEdit, m: Maybe<&2, List<&2, ItemEdit>>) -> Maybe<&2, List<&2, ItemEdit>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{e <> es}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: union states what a merge applies, and no code that runs calls it
# the edit scripts e1 and e2 over one base, as one script that makes the
# changes of both: an insertion of one side is made; one insertion of both,
# when they insert the same item; a base item is removed when one side removes
# it, and kept when both keep it. None when they insert different items at one
# point, or do not fit one base
def union(+e1: List<&2, ItemEdit>, +e2: List<&2, ItemEdit>) -> Maybe<&2, List<&2, ItemEdit>>:
  match e1:
    case Nil{}:
      match e2:
        case Nil{}:
          Some{[]}
        case Con{ItemInserted{z}, r2}:
          edit_some(ItemInserted{z}, union(e1, r2))
        case _:
          None{}
    case Con{ItemInserted{+y}, r1}:
      match e2:
        case Con{ItemInserted{z}, r2}:
          Bool.pick(
            Maybe<&2, List<&2, ItemEdit>>,
            same_item(y, z),
            edit_some(ItemInserted{y}, union(r1, r2)),
            None{}
          )
        case _:
          edit_some(ItemInserted{y}, union(r1, e2))
    case Con{ItemKept{}, r1}:
      match e2:
        case Con{ItemInserted{z}, r2}:
          edit_some(ItemInserted{z}, union(e1, r2))
        case Con{ItemKept{}, r2}:
          edit_some(ItemKept{}, union(r1, r2))
        case Con{ItemRemoved{}, r2}:
          edit_some(ItemRemoved{}, union(r1, r2))
        case Nil{}:
          None{}
    case Con{ItemRemoved{}, r1}:
      match e2:
        case Con{ItemInserted{z}, r2}:
          edit_some(ItemInserted{z}, union(e1, r2))
        case Con{ItemKept{}, r2}:
          edit_some(ItemRemoved{}, union(r1, r2))
        case Con{ItemRemoved{}, r2}:
          edit_some(ItemRemoved{}, union(r1, r2))
        case Nil{}:
          None{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the edit script from the items a to the items b
law ItemMerge.diff:
  for a: List<&2, List<&2, U32>>
  for b: List<&2, List<&2, U32>>
  List<&2, ItemEdit>

# the merge of ours and theirs, two changes of base; None when they clash
law ItemMerge.merge:
  for base: List<&2, List<&2, U32>>
  for ours: List<&2, List<&2, U32>>
  for theirs: List<&2, List<&2, U32>>
  Maybe<&2, List<&2, List<&2, U32>>>

# Laws
# ----

# Means: the diff from a to b, applied to a, gives b.
# For free: a diff of a list with itself changes nothing; diffs say exactly how
# one list became another.
# For the goal: diffs follow the items of a format (Resource), so a change is
# told item by item.
# Example: the diff from [a, b] to [a, c, b], applied to [a, b], gives
# [a, c, b].
law ItemMerge.diff_applies:
  for a: List<&2, List<&2, U32>>
  for b: List<&2, List<&2, U32>>
  {apply(ItemMerge.diff(a, b), a) == Some{b}: Maybe<&2, List<&2, List<&2, U32>>>}

# Means: a diff keeps as many items as a longest list that both hold in order.
# For free: a diff never removes an item that it could keep, so two changes
# clash only when they really touch the same items; the diff of a list with
# itself keeps everything.
# For the goal: two writers who change different items of a file merge without
# a conflict (Branch: merges go resource by resource).
# Example: the diff from [a, b, c] to [a, x, c] keeps a and c.
law ItemMerge.diff_keeps_most:
  for a: List<&2, List<&2, U32>>
  for b: List<&2, List<&2, U32>>
  {kept(ItemMerge.diff(a, b)) == lcs_length(a, b): Nat}

# Means: when the changes from base to ours and from base to theirs are apart
# (no hunk of one touches a differing hunk of the other), the merge is the base
# after the one edit script that makes the changes of both.
# For free: a merge never loses a change made on only one side; when ours did
# not change, the merge is theirs, and the other way around; when both made the
# same change, the merge is that change.
# For the goal: a merge never loses a change made on only one side (Resource).
# Example: base [a, b, c], ours [x, b, c], theirs [a, b, y]: the merge is
# [x, b, y].
law ItemMerge.merge_apart:
  for base: List<&2, List<&2, U32>>
  for ours: List<&2, List<&2, U32>>
  for theirs: List<&2, List<&2, U32>>
  {clash(hunks(ItemMerge.diff(base, ours)), hunks(ItemMerge.diff(base, theirs))) == False{}: Bool}
    -> Exists(
      List<&2, ItemEdit>,
      u => {
        union(
          ItemMerge.diff(base, ours),
          ItemMerge.diff(base, theirs)
        )
          == Some{u}: Maybe<&2, List<&2, ItemEdit>>
      }
        & {
          ItemMerge.merge(base, ours, theirs) == apply(u, base): Maybe<&2, List<&2, List<&2, U32>>>
        }
    )

# Means: when a change of ours and a change of theirs touch or overlap and
# differ, the merge clashes.
# For free: a merge never picks one side's change over the other's; a clash is
# always a real meeting of two changes.
# For the goal: a conflict is stored and shared, and resolved by a writer
# (Branch).
# Example: base [a], ours [x], theirs [y]: the merge clashes.
law ItemMerge.merge_clashes_when_close:
  for base: List<&2, List<&2, U32>>
  for ours: List<&2, List<&2, U32>>
  for theirs: List<&2, List<&2, U32>>
  {clash(hunks(ItemMerge.diff(base, ours)), hunks(ItemMerge.diff(base, theirs))) == True{}: Bool}
    -> {ItemMerge.merge(base, ours, theirs) == None{}: Maybe<&2, List<&2, List<&2, U32>>>}
