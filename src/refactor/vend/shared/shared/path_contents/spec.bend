import Base
import ../../../../shared/shared/shared/shared/shared/part_store/spec.bend as PartStore
import ../../../../shared/shared/shared/shared/shared/shared/association_list/spec.bend as AssociationList
import ../../../../shared/shared/shared/shared/shared/shared/shared/shared.bend as Shared
import ../../../../shared/shared/shared/shared/shared/shared/word_list_sets/spec.bend as WordListSets

# Path contents: the whole content of a version, as pairs, in path order, of a
# path and its entry: a resource (the name of its reader and the hash of its
# content, kept as parts) or a conflict of three entries that a merge could not
# join. A writer changes paths; a three-way merge goes path by path: theirs when
# ours did not change, ours when theirs did not change or both made the same
# change, else the merge of the three contents in their reader (a hook, which
# may lack parts and answer unknown), else a conflict that keeps all three
# sides. So a change made on only one side is never lost, and a conflict can be
# shared and resolved by anyone.

# Entries
# -------

# a present resource: the name of its reader, and the hash of its content
type Resource is Data:
  Resource{reader: List<&2, U32>, content: Shared.FixedLengthList(U32, 8n)}

# what a path holds: nothing, a resource, or a conflict of the base, ours and
# theirs that a merge could not join
type PathEntry is Data:
  EntryAbsent{}
  EntryPresent{resource: Resource}
  EntryConflict{base: PathEntry, ours: PathEntry, theirs: PathEntry}

# the hashes ha and hb are the same, where readers_same says whether their
# resources have one reader: false when they do not
def Resource.same.then(
  readers_same: Bool,
  ha: Shared.FixedLengthList(U32, 8n),
  hb: Shared.FixedLengthList(U32, 8n)
) -> Bool:
  match readers_same:
    case True{}:
      PartStore.same_hash(ha, hb)
    case False{}:
      False{}

# the resources a and b are the same
def Resource.same(a: Resource, b: Resource) -> Bool:
  match a b:
    case Resource{ra, ha} Resource{rb, hb}:
      Resource.same.then(WordListSets.same(ra, rb), ha, hb)

# the resources a and b have the same reader
def Resource.same_reader(a: Resource, b: Resource) -> Bool:
  match a b:
    case Resource{ra, ha} Resource{rb, hb}:
      WordListSets.same(ra, rb)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an entry nests one conflict for each merge that clashed on its path and was not resolved, so it is a few levels deep: comparing every side costs at most the size of the two entries
# the entries a and b are the same
def PathEntry.same(a: PathEntry, b: PathEntry) -> Bool:
  match a b:
    case EntryAbsent{} EntryAbsent{}:
      True{}
    case EntryPresent{x} EntryPresent{y}:
      Resource.same(x, y)
    case EntryConflict{b1, o1, t1} EntryConflict{b2, o2, t2}:
      Bool.and(PathEntry.same(b1, b2), Bool.and(PathEntry.same(o1, o2), PathEntry.same(t1, t2)))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the entry e is a conflict
def PathEntry.is_conflict(e: PathEntry) -> Bool:
  match e:
    case EntryConflict{b, o, t}:
      True{}
    case _:
      False{}

# the entry of the resource x, absent when x is not there
def PathEntry.of_resource(x: Maybe<&2, Resource>) -> PathEntry:
  match x:
    case None{}:
      EntryAbsent{}
    case Some{r}:
      EntryPresent{r}

# the entry that a content stores as x: absent when it stores nothing
def PathEntry.of_stored(x: Maybe<&2, PathEntry>) -> PathEntry:
  match x:
    case None{}:
      EntryAbsent{}
    case Some{e}:
      e

# what a content stores for the entry e: nothing for an absent entry
def PathEntry.stored(e: PathEntry) -> Maybe<&2, PathEntry>:
  match e:
    case EntryAbsent{}:
      None{}
    case e:
      Some{e}

# the entry of the path p in the content c
def Content.entry_at(
  c: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  p: List<&2, U32>
) -> PathEntry:
  PathEntry.of_stored(AssociationList.value_of_first_entry_with_key(~PathEntry, c, p))

# the content c with the entry e at the path p
def Content.with_entry(
  c: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  p: List<&2, U32>,
  e: PathEntry
) -> List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>:
  AssociationList.with_entry(~PathEntry, c, p, PathEntry.stored(e))

# a change that a writer asks for: the resource at a path (none removes it)
type Change is Data:
  Change{path: List<&2, U32>, resource: Maybe<&2, Resource>}

# the content c after the changes cs, one after another
def Content.with_changes(
  cs: List<&2, Change>,
  c: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
) -> List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>:
  match cs:
    case Nil{}:
      c
    case Con{Change{p, x}, rest}:
      Content.with_changes(rest, Content.with_entry(c, p, PathEntry.of_resource(x)))

# Merging
# -------

# what the content merge hook gives for three contents: unknown (it lacks
# parts that it needs), a clash, or the hash of the merged content
type ContentMerge is Data:
  ContentMergeUnknown{}
  ContentMergeClash{}
  ContentMerged{content: Shared.FixedLengthList(U32, 8n)}

# the content merge hook: the merge of the contents of the hashes base, ours
# and theirs, read by the reader of a name
def ContentMergeHook() -> Type:
  List<
    &2,
    U32> -> Shared.FixedLengthList(
    U32,
    8n
  ) -> Shared.FixedLengthList(U32, 8n) -> Shared.FixedLengthList(U32, 8n) -> ContentMerge

# the merge of the entries of one path: unknown, or the merged entry and
# whether it clashed
type EntryMerge is Data:
  EntryMergeUnknown{}
  EntryMerged{entry: PathEntry, clashed: Bool}

# the entry of the merge m, absent when it is unknown
def EntryMerge.entry(m: EntryMerge) -> PathEntry:
  match m:
    case EntryMergeUnknown{}:
      EntryAbsent{}
    case EntryMerged{e, c}:
      e

# the merge m clashed
def EntryMerge.clashed(m: EntryMerge) -> Bool:
  match m:
    case EntryMergeUnknown{}:
      False{}
    case EntryMerged{e, c}:
      c

# the conflict of the resources b, o and t
def EntryMerge.conflict(b: Resource, o: Resource, t: Resource) -> EntryMerge:
  EntryMerged{EntryConflict{EntryPresent{b}, EntryPresent{o}, EntryPresent{t}}, True{}}

# the entry merge that the content merge m of the resources b, o and t gives,
# where o and t are read by the reader of the name r
def EntryMerge.of_content_merge(
  m: ContentMerge,
  r: List<&2, U32>,
  b: Resource,
  o: Resource,
  t: Resource
) -> EntryMerge:
  match m:
    case ContentMergeUnknown{}:
      EntryMergeUnknown{}
    case ContentMergeClash{}:
      EntryMerge.conflict(b, o, t)
    case ContentMerged{h}:
      EntryMerged{EntryPresent{Resource{r, h}}, False{}}

# the merge of the resources b, o and t, by the content merge hook
def PathEntry.merge.by_hook(
  ~merge_content: ContentMergeHook(),
  b: Resource,
  o: Resource,
  t: Resource
) -> EntryMerge:
  match b o t:
    case Resource{rb, +hb} Resource{+r, +ho} Resource{rt, +ht}:
      EntryMerge.of_content_merge(
        merge_content(r, hb, ho, ht),
        r,
        Resource{rb, hb},
        Resource{r, ho},
        Resource{rt, ht}
      )

# the merge of the resources b, o and t, where same_reader says whether o and t
# have one reader: by the hook when they do, a clash when they do not
def PathEntry.merge.of_reader(
  ~merge_content: ContentMergeHook(),
  same_reader: Bool,
  b: Resource,
  o: Resource,
  t: Resource
) -> EntryMerge:
  match same_reader:
    case True{}:
      PathEntry.merge.by_hook(~merge_content, b, o, t)
    case False{}:
      EntryMerge.conflict(b, o, t)

# the merge of the entries b, o and t, none the same as another: by their
# reader when all three are resources, a clash otherwise
def PathEntry.merge.of_contents(
  ~merge_content: ContentMergeHook(),
  b: PathEntry,
  o: PathEntry,
  t: PathEntry
) -> EntryMerge:
  match b o t:
    case EntryPresent{x} EntryPresent{+y} EntryPresent{+z}:
      PathEntry.merge.of_reader(~merge_content, Resource.same_reader(y, z), x, y, z)
    case b o t:
      EntryMerged{EntryConflict{b, o, t}, True{}}

# the merge of the entries b, o and t, where same says whether o and t are the
# same
def PathEntry.merge.same_change(
  ~merge_content: ContentMergeHook(),
  same: Bool,
  b: PathEntry,
  o: PathEntry,
  t: PathEntry
) -> EntryMerge:
  match same:
    case True{}:
      EntryMerged{o, False{}}
    case False{}:
      PathEntry.merge.of_contents(~merge_content, b, o, t)

# the merge of the entries b, o and t, where unchanged says whether t is b
def PathEntry.merge.theirs_unchanged(
  ~merge_content: ContentMergeHook(),
  unchanged: Bool,
  b: PathEntry,
  +o: PathEntry,
  +t: PathEntry
) -> EntryMerge:
  match unchanged:
    case True{}:
      EntryMerged{o, False{}}
    case False{}:
      PathEntry.merge.same_change(~merge_content, PathEntry.same(o, t), b, o, t)

# the merge of the entries b, o and t, where unchanged says whether o is b
def PathEntry.merge.ours_unchanged(
  ~merge_content: ContentMergeHook(),
  unchanged: Bool,
  +b: PathEntry,
  o: PathEntry,
  +t: PathEntry
) -> EntryMerge:
  match unchanged:
    case True{}:
      EntryMerged{t, False{}}
    case False{}:
      PathEntry.merge.theirs_unchanged(~merge_content, PathEntry.same(t, b), b, o, t)

# the merge of ours and theirs, two changes of the entry base of one path:
# theirs when ours did not change, ours when theirs did not change or both made
# the same change, else the merge of their contents by the hook when all three
# are resources and ours and theirs have one reader, else a conflict of the
# three
def PathEntry.merge(
  ~merge_content: ContentMergeHook(),
  +base: PathEntry,
  +ours: PathEntry,
  theirs: PathEntry
) -> EntryMerge:
  PathEntry.merge.ours_unchanged(~merge_content, PathEntry.same(ours, base), base, ours, theirs)

# the merge of three contents: unknown, or the merged content and the paths
# that clashed
type ContentsMerge is Data:
  ContentsMergeUnknown{}
  ContentsMerged{
    content: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
    clashes: List<&2, List<&2, U32>>
  }

# the merge acc with the merge m of the path p
def Content.merge.add(+p: List<&2, U32>, m: EntryMerge, acc: ContentsMerge) -> ContentsMerge:
  match m acc:
    case EntryMerged{e, c} ContentsMerged{xs, +cs}:
      ContentsMerged{
        Content.with_entry(xs, p, e),
        Bool.pick(List<&2, List<&2, U32>>, c, p <> cs, cs)
      }
    case _ _:
      ContentsMergeUnknown{}

# the merge acc with the merges of the paths ps of the contents b, o and t
def Content.merge.go(
  ~merge_content: ContentMergeHook(),
  ps: List<&2, List<&2, U32>>,
  +b: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  +o: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  +t: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  acc: ContentsMerge
) -> ContentsMerge:
  match ps:
    case Nil{}:
      acc
    case Con{+p, rest}:
      Content.merge.go(
        ~merge_content,
        rest,
        b,
        o,
        t,
        Content.merge.add(
          p,
          PathEntry.merge(
            ~merge_content,
            Content.entry_at(b, p),
            Content.entry_at(o, p),
            Content.entry_at(t, p)
          ),
          acc
        )
      )

# the paths of the contents b, o and t, each once
def Content.paths(
  b: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  o: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  t: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
) -> List<&2, List<&2, U32>>:
  WordListSets.dedupe(
    List.append(
      &2,
      List<&2, U32>,
      AssociationList.keys(~PathEntry, b),
      List.append(
        &2,
        List<&2, U32>,
        AssociationList.keys(~PathEntry, o),
        AssociationList.keys(~PathEntry, t)
      )
    )
  )

# the merge of ours and theirs, two changes of the content base, path by path
def Content.merge(
  ~merge_content: ContentMergeHook(),
  +base: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  +ours: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>,
  +theirs: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
) -> ContentsMerge:
  Content.merge.go(
    ~merge_content,
    Content.paths(base, ours, theirs),
    base,
    ours,
    theirs,
    ContentsMerged{[], []}
  )

# Helpers of the laws
# -------------------

# the content merge hook merge_content2 knows at least what merge_content
# knows: where merge_content knows, it gives the same
def ContentMerge.KnowsMore(
  ~merge_content: ContentMergeHook(),
  ~merge_content2: ContentMergeHook()
) -> Type:
  @r: List<
    &2,
    U32> -> @b: Shared.FixedLengthList(
    U32,
    8n
  ) -> @o: Shared.FixedLengthList(
    U32,
    8n
  ) -> @t: Shared.FixedLengthList(
    U32,
    8n
  ) -> ({merge_content(r, b, o, t) == ContentMergeUnknown{}: ContentMerge} -> Empty)
    -> {merge_content2(r, b, o, t) == merge_content(r, b, o, t): ContentMerge}

# the content merge hook always knows: it never lacks a part
def ContentMerge.AlwaysKnows(~merge_content: ContentMergeHook()) -> Type:
  @r: List<
    &2,
    U32> -> @b: Shared.FixedLengthList(
    U32,
    8n
  ) -> @o: Shared.FixedLengthList(
    U32,
    8n
  ) -> @t: Shared.FixedLengthList(
    U32,
    8n
  ) -> {merge_content(r, b, o, t) == ContentMergeUnknown{}: ContentMerge}
    -> Empty

# Laws
# ----

# Means: the merge of one path takes theirs when ours did not change, ours when
# theirs did not change, and ours when both made the same change; otherwise,
# when all three are resources and ours and theirs have one reader, it is what
# the content merge hook gives (the merged resource in that reader, a conflict
# of the three, or unknown); otherwise it is a conflict of the three.
# For free: a change made on only one side is never lost; a conflict keeps
# base, ours and theirs, so nothing is lost and anyone can resolve it; a write
# that saw a conflict, onto a line where the path did not change since,
# replaces it; a deletion against a change clashes.
# For the goal: merges go resource by resource, each in its own reader, and a
# conflict is stored and shared (Branch, Resource).
# Example: base "a" (lines), ours "a", theirs "b": the merge is "b". Base
# absent, ours "a", theirs "b": a conflict of the three.
law PathContents.entry_merge_keeps_every_change:
  for ~merge_content: ContentMergeHook()
  for b: PathEntry
  for o: PathEntry
  for t: PathEntry
  (
    {
      PathEntry.same(o, b) == True{}: Bool
    } -> {PathEntry.merge(~merge_content, b, o, t) == EntryMerged{t, False{}}: EntryMerge}
  )
    & (
      (
        {
          PathEntry.same(o, b) == False{}: Bool
        } -> {
          PathEntry.same(t, b) == True{}: Bool
        } -> {PathEntry.merge(~merge_content, b, o, t) == EntryMerged{o, False{}}: EntryMerge}
      )
        & (
          (
            {
              PathEntry.same(o, b) == False{}: Bool
            } -> {
              PathEntry.same(t, b) == False{}: Bool
            } -> {
              PathEntry.same(o, t) == True{}: Bool
            } -> {PathEntry.merge(~merge_content, b, o, t) == EntryMerged{o, False{}}: EntryMerge}
          )
            & (
              {
                PathEntry.same(o, b) == False{}: Bool
              } -> {
                PathEntry.same(t, b) == False{}: Bool
              } -> {
                PathEntry.same(o, t) == False{}: Bool
              } -> {
                PathEntry.merge(
                  ~merge_content,
                  b,
                  o,
                  t
                )
                  == PathEntry.merge.of_contents(~merge_content, b, o, t): EntryMerge
              }
                & (
                  (
                    @rb: List<
                      &2,
                      U32> -> @hb: Shared.FixedLengthList(
                      U32,
                      8n
                    ) -> @r: List<
                      &2,
                      U32> -> @ho: Shared.FixedLengthList(
                      U32,
                      8n
                    ) -> @ht: Shared.FixedLengthList(
                      U32,
                      8n
                    ) -> {
                      b == EntryPresent{Resource{rb, hb}}: PathEntry
                    } -> {
                      o == EntryPresent{Resource{r, ho}}: PathEntry
                    } -> {
                      t == EntryPresent{Resource{r, ht}}: PathEntry
                    } -> {
                      PathEntry.merge.of_contents(
                        ~merge_content,
                        b,
                        o,
                        t
                      )
                        == EntryMerge.of_content_merge(
                          merge_content(r, hb, ho, ht),
                          r,
                          Resource{rb, hb},
                          Resource{r, ho},
                          Resource{r, ht}
                        ): EntryMerge
                    }
                  )
                    & (
                      @e: PathEntry -> {
                        PathEntry.merge.of_contents(
                          ~merge_content,
                          b,
                          o,
                          t
                        )
                          == EntryMerged{e, True{}}: EntryMerge
                      } -> {e == EntryConflict{b, o, t}: PathEntry}
                    )
                )
            )
        )
    )

# Means: the merge of three contents goes path by path: it is unknown exactly
# when the merge of some path is unknown; otherwise its content holds, at every
# path, the entry of the merge of that path, in path order, and its clashes are
# exactly the paths whose merge clashed, each once.
# For free: paths that no side changed stay; the merge of a content with
# itself is that content; the order of the paths never matters.
# For the goal: merges go resource by resource (Branch), and a merge never
# loses a change made on only one side (Resource).
# Example: base [a.txt "x"], ours [a.txt "x", b.txt "y"], theirs [] (a.txt
# deleted): the merge is [b.txt "y"], with no clash.
law PathContents.merge_goes_path_by_path:
  for ~merge_content: ContentMergeHook()
  for b: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
  for o: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
  for t: List<&2, +Sigma<List<&2, U32>, _ => PathEntry>>
  (
    {
      Content.merge(~merge_content, b, o, t) == ContentsMergeUnknown{}: ContentsMerge
    } -> Exists(
      List<&2, U32>,
      p => {
        PathEntry.merge(
          ~merge_content,
          Content.entry_at(b, p),
          Content.entry_at(o, p),
          Content.entry_at(t, p)
        )
          == EntryMergeUnknown{}: EntryMerge
      }
    )
  )
    & (
      (
        @p: List<
          &2,
          U32> -> {
          PathEntry.merge(
            ~merge_content,
            Content.entry_at(b, p),
            Content.entry_at(o, p),
            Content.entry_at(t, p)
          )
            == EntryMergeUnknown{}: EntryMerge
        } -> {Content.merge(~merge_content, b, o, t) == ContentsMergeUnknown{}: ContentsMerge}
      )
        & (
          @c: List<
            &2,
            +Sigma<
              List<&2, U32>,
              _ => PathEntry>> -> @cs: List<
            &2,
            List<
              &2,
              U32>> -> {
            Content.merge(~merge_content, b, o, t) == ContentsMerged{c, cs}: ContentsMerge
          } -> {
            AssociationList.keys_strictly_increase(~PathEntry, c) == True{}: Bool
          }
            & (
              WordListSets.Distinct(
                cs
              )
                & (
                  @p: List<
                    &2,
                    U32> -> {
                    Content.entry_at(
                      c,
                      p
                    )
                      == EntryMerge.entry(
                        PathEntry.merge(
                          ~merge_content,
                          Content.entry_at(b, p),
                          Content.entry_at(o, p),
                          Content.entry_at(t, p)
                        )
                      ): PathEntry
                  }
                    & {
                      WordListSets.contains(
                        cs,
                        p
                      )
                        == EntryMerge.clashed(
                          PathEntry.merge(
                            ~merge_content,
                            Content.entry_at(b, p),
                            Content.entry_at(o, p),
                            Content.entry_at(t, p)
                          )
                        ): Bool
                    }
                )
            )
        )
    )
