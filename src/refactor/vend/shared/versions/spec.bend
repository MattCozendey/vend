import Base
import ../../../shared/shared/shared/shared/shared/shared/association_list/spec.bend as AssociationList
import ../../../shared/shared/shared/shared/shared/shared/shared/shared.bend as Shared
import ../../../shared/shared/shared/shared/shared/shared/word_list_sets/spec.bend as WordListSets
import ../shared/path_contents/spec.bend as PathContents

# Versions: the history of one line (a branch) from the requests that its
# owner group decided, in order. A version is the whole content of the line
# after one decided change (see path_contents); version 0 of every line is
# empty. A write changes paths from the version that its writer saw; a merge
# brings in a version of any line from a base that both sides include; both
# merge path by path onto the newest content. A move makes a version equal to
# any version; a mark names a version for good. A request counts once. A
# conflict stays until a later version holds its path without one. When a
# request needs data that a node does not hold yet (a version of another line,
# parts for a content merge), the history waits before it until the data is
# there.

# Versions
# --------

# version count of the line line: count 0 is empty, count n is the content
# after its n-th decided change
type Point is Data:
  Point{line: List<&2, U32>, count: Nat}

# what a version holds: its content, and its frontier: for each line, how many
# of its versions the version includes
type View is Data:
  View{
    content: List<&2, +Sigma<List<&2, U32>, _ => PathContents.PathEntry>>,
    frontier: List<&2, +Sigma<List<&2, U32>, _ => Nat>>
  }

# the view of version 0 of any line: no content, no line
def View.empty() -> View:
  View{[], []}

# the content of the view v
def View.content(v: View) -> List<&2, +Sigma<List<&2, U32>, _ => PathContents.PathEntry>>:
  match v:
    case View{c, f}:
      c

# the frontier of the view v
def View.frontier(v: View) -> List<&2, +Sigma<List<&2, U32>, _ => Nat>>:
  match v:
    case View{c, f}:
      f

# the view x, or the empty view when x is not there
def View.or_empty(x: Maybe<&2, View>) -> View:
  match x:
    case None{}:
      View.empty()
    case Some{v}:
      v

# the number n, or 0 when it is not there
def Frontier.count_or_zero(x: Maybe<&2, Nat>) -> Nat:
  match x:
    case None{}:
      0n
    case Some{n}:
      n

# how many versions of the line l the frontier fs includes
def Frontier.count_of(fs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>, l: List<&2, U32>) -> Nat:
  Frontier.count_or_zero(AssociationList.value_of_first_entry_with_key(~Nat, fs, l))

# the frontier fs includes the version p
def Frontier.includes(fs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>, p: Point) -> Bool:
  match p:
    case Point{l, n}:
      Nat.is_le(n, Frontier.count_of(fs, l))

# the frontier theirs includes the version p, where ours_includes says
# whether the other frontier does: false when it does not
def Frontier.both_include.then(
  ours_includes: Bool,
  theirs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  p: Point
) -> Bool:
  match ours_includes:
    case True{}:
      Frontier.includes(theirs, p)
    case False{}:
      False{}

# the frontiers ours and theirs both include the version p
def Frontier.both_include(
  ours: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  theirs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  +p: Point
) -> Bool:
  Frontier.both_include.then(Frontier.includes(ours, p), theirs, p)

# the frontier fs with the frontier gs: for each line, the most versions that
# either includes
def Frontier.join(
  gs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  +fs: List<&2, +Sigma<List<&2, U32>, _ => Nat>>
) -> List<&2, +Sigma<List<&2, U32>, _ => Nat>>:
  match gs:
    case Nil{}:
      fs
    case Con{(+l, n), rest}:
      Frontier.join(
        rest,
        AssociationList.with_entry(~Nat, fs, l, Some{Nat.max(n, Frontier.count_of(fs, l))})
      )

# the versions p and q are the same
def Point.same(p: Point, q: Point) -> Bool:
  match p q:
    case Point{lp, np} Point{lq, nq}:
      Bool.and(WordListSets.same(lp, lq), Nat.is_eq(np, nq))

# the view of a version of another line, which a node holds
type KnownView is Data:
  KnownView{point: Point, view: View}

# found, or the view of the version p among the known views ks
def KnownViews.view_of.go(
  ks: List<&2, KnownView>,
  +p: Point,
  found: Maybe<&2, View>
) -> Maybe<&2, View>:
  match ks:
    case Nil{}:
      found
    case Con{KnownView{q, v}, rest}:
      match found:
        case Some{x}:
          Some{x}
        case None{}:
          KnownViews.view_of.go(rest, p, Shared.Maybe.when(~View, Point.same(q, p), Some{v}))

# the view of the version p among the known views ks, if it is there
def KnownViews.view_of(ks: List<&2, KnownView>, p: Point) -> Maybe<&2, View>:
  KnownViews.view_of.go(ks, p, None{})

# a request is named by its writer (a public key) and the id that the writer
# gave it
type RequestId is Data:
  RequestId{writer: List<&2, U32>, id: List<&2, U32>}

# the ids ia and ib are the same, where writers_same says whether their
# requests have one writer: false when they do not
def RequestId.same.then(writers_same: Bool, ia: List<&2, U32>, ib: List<&2, U32>) -> Bool:
  match writers_same:
    case True{}:
      WordListSets.same(ia, ib)
    case False{}:
      False{}

# the request ids a and b are the same
def RequestId.same(a: RequestId, b: RequestId) -> Bool:
  match a b:
    case RequestId{wa, ia} RequestId{wb, ib}:
      RequestId.same.then(WordListSets.same(wa, wb), ia, ib)

# what a writer asks of a line. RequestWrite: the changes, from version base of
# the line, which the writer saw. RequestMerge: bring in the version from, from
# the version base, which both sides must include. RequestMove: a new version
# equal to the version to. RequestMark: the name name for version version of
# the line
type BranchRequest is Data:
  RequestWrite{base: Nat, changes: List<&2, PathContents.Change>}
  RequestMerge{from: Point, base: Point}
  RequestMove{to: Point}
  RequestMark{name: List<&2, U32>, version: Nat}

# a request that the owner group of the line decided, with its id
type DecidedRequest is Data:
  DecidedRequest{id: RequestId, request: BranchRequest}

# a version: the request that made it, what it holds, and the versions that it
# comes from
type Version is Data:
  Version{made_by: RequestId, view: View, parents: List<&2, Point>}

# the view of the version v
def Version.view(v: Version) -> View:
  match v:
    case Version{i, x, ps}:
      x

# what became of a decided request: it made the version number, with the paths
# clashes in conflict; it set a mark; it asked to set a mark that names a
# version already (Stale); or it named a version of the line that does not
# exist, or a merge base that a side does not include (Refused)
type Outcome is Data:
  OutcomeMadeVersion{number: Nat, clashes: List<&2, List<&2, U32>>}
  OutcomeMarked{}
  OutcomeStale{}
  OutcomeRefused{}

# the outcome of the request of the id id
type Decision is Data:
  Decision{id: RequestId, outcome: Outcome}

# the history of a line: its versions, newest first (version 0, empty, is not
# listed); its marks, a name and a version number each, in name order; the
# outcomes of its requests, newest first; and whether it waits for data that it
# does not hold, before the next request
type LineHistory is Data:
  LineHistory{
    versions: List<&2, Version>,
    marks: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
    decisions: List<&2, Decision>,
    waiting: Bool
  }

# the history with no request
def LineHistory.empty() -> LineHistory:
  LineHistory{[], [], [], False{}}

# the versions of the history h, newest first
def LineHistory.versions(h: LineHistory) -> List<&2, Version>:
  match h:
    case LineHistory{vs, ms, ds, w}:
      vs

# the marks of the history h
def LineHistory.marks(h: LineHistory) -> List<&2, +Sigma<List<&2, U32>, _ => Nat>>:
  match h:
    case LineHistory{vs, ms, ds, w}:
      ms

# the decisions of the history h, newest first
def LineHistory.decisions(h: LineHistory) -> List<&2, Decision>:
  match h:
    case LineHistory{vs, ms, ds, w}:
      ds

# the history h waits for data that it does not hold
def LineHistory.waiting(h: LineHistory) -> Bool:
  match h:
    case LineHistory{vs, ms, ds, w}:
      w

# how many versions the history h has after version 0: the number of its newest
def LineHistory.count(h: LineHistory) -> Nat:
  List.length(&2, Version, LineHistory.versions(h))

# the view of the first of the versions vs, or the empty view
def Versions.newest_view(vs: List<&2, Version>) -> View:
  match vs:
    case Nil{}:
      View.empty()
    case Con{v, rest}:
      Version.view(v)

# the view of the newest version of the history h
def LineHistory.newest(h: LineHistory) -> View:
  Versions.newest_view(LineHistory.versions(h))

# the view of the version k places after the first of vs, if there is one
def Versions.view_from_newest(vs: List<&2, Version>, k: Nat) -> Maybe<&2, View>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, rest}:
      match k:
        case 0n:
          Some{Version.view(v)}
        case 1n+j:
          Versions.view_from_newest(rest, j)

# the view of version n of the history h, if it has one
def LineHistory.view_at(+h: LineHistory, +n: Nat) -> Maybe<&2, View>:
  Bool.pick(
    Maybe<&2, View>,
    Nat.is_eq(n, 0n),
    Some{View.empty()},
    Shared.Maybe.when(
      ~View,
      Nat.is_le(n, LineHistory.count(h)),
      Versions.view_from_newest(LineHistory.versions(h), Nat.sub(LineHistory.count(h), n))
    )
  )

# the content of version n of the history h, empty when it has none
def LineHistory.content_at(
  h: LineHistory,
  n: Nat
) -> List<&2, +Sigma<List<&2, U32>, _ => PathContents.PathEntry>>:
  View.content(View.or_empty(LineHistory.view_at(h, n)))

# the outcome of the request id among the decisions ds, after found
def Decisions.outcome_of.go(
  ds: List<&2, Decision>,
  +i: RequestId,
  found: Maybe<&2, Outcome>
) -> Maybe<&2, Outcome>:
  match ds:
    case Nil{}:
      found
    case Con{Decision{j, o}, rest}:
      match found:
        case Some{x}:
          Some{x}
        case None{}:
          Decisions.outcome_of.go(
            rest,
            i,
            Shared.Maybe.when(~Outcome, RequestId.same(j, i), Some{o})
          )

# the outcome of the request id among the decisions ds, if it was decided
def Decisions.outcome_of(ds: List<&2, Decision>, i: RequestId) -> Maybe<&2, Outcome>:
  Decisions.outcome_of.go(ds, i, None{})

# the request id is among the decisions ds
def Decisions.has(ds: List<&2, Decision>, i: RequestId) -> Bool:
  Maybe.is_some(&2, Outcome, Decisions.outcome_of(ds, i))

# Steps
# -----

# where a request points: data that the node does not hold yet, outside the
# line (a version that it does not have), or a version, with its view
type PointLookup is Data:
  PointUnknown{}
  PointOutside{}
  PointFound{view: View}

# the lookup of a version of the line itself, whose view is x if it has one
def PointLookup.of_own(x: Maybe<&2, View>) -> PointLookup:
  match x:
    case None{}:
      PointOutside{}
    case Some{v}:
      PointFound{v}

# the lookup of a version of another line, whose view is x if the node holds it
def PointLookup.of_other(x: Maybe<&2, View>) -> PointLookup:
  match x:
    case None{}:
      PointUnknown{}
    case Some{v}:
      PointFound{v}

# the lookup of version n of the line l, which is not the line of the history,
# where others are the views of other lines that the node holds
def PointLookup.other_line(others: List<&2, KnownView>, l: List<&2, U32>, n: Nat) -> PointLookup:
  match n:
    case 0n:
      PointFound{View.empty()}
    case 1n+m:
      PointLookup.of_other(KnownViews.view_of(others, Point{l, 1n+m}))

# the lookup of version n of the line l, where own says whether l is the line
# of the history h
def PointLookup.on_line(
  own: Bool,
  others: List<&2, KnownView>,
  h: LineHistory,
  l: List<&2, U32>,
  n: Nat
) -> PointLookup:
  match own:
    case True{}:
      PointLookup.of_own(LineHistory.view_at(h, n))
    case False{}:
      PointLookup.other_line(others, l, n)

# the lookup of the version p, from the history h of the line line
def LineHistory.lookup(
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  h: LineHistory,
  p: Point
) -> PointLookup:
  match p:
    case Point{+l, n}:
      PointLookup.on_line(WordListSets.same(l, line), others, h, l, n)

# the history h with the outcome o of the request i
def LineHistory.decide(h: LineHistory, i: RequestId, o: Outcome) -> LineHistory:
  match h:
    case LineHistory{vs, ms, ds, w}:
      LineHistory{vs, ms, Decision{i, o} <> ds, w}

# the history h, waiting for data that it does not hold
def LineHistory.wait(h: LineHistory) -> LineHistory:
  match h:
    case LineHistory{vs, ms, ds, w}:
      LineHistory{vs, ms, ds, True{}}

# the history h with the version v and the decision d
def LineHistory.add(h: LineHistory, v: Version, d: Decision) -> LineHistory:
  match h:
    case LineHistory{vs, ms, ds, w}:
      LineHistory{v <> vs, ms, d <> ds, w}

# the history h of the line line after the request i makes a version from the
# merge m, with the parents parents and the frontier frontier (to which the new
# version adds itself); it waits when m is unknown
def LineHistory.make(
  line: List<&2, U32>,
  +h: LineHistory,
  +i: RequestId,
  parents: List<&2, Point>,
  frontier: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  m: PathContents.ContentsMerge
) -> LineHistory:
  match m:
    case PathContents.ContentsMergeUnknown{}:
      LineHistory.wait(h)
    case PathContents.ContentsMerged{c, cs}:
      LineHistory.add(
        h,
        Version{
          i,
          View{c, AssociationList.with_entry(~Nat, frontier, line, Some{1n+LineHistory.count(h)})},
          parents
        },
        Decision{i, OutcomeMadeVersion{1n+LineHistory.count(h), cs}}
      )

# the history h of the line line after the write i of the changes changes from
# the content base
def LineHistory.write.from(
  ~merge_content: PathContents.ContentMergeHook(),
  +line: List<&2, U32>,
  +h: LineHistory,
  i: RequestId,
  +base: List<&2, +Sigma<List<&2, U32>, _ => PathContents.PathEntry>>,
  changes: List<&2, PathContents.Change>
) -> LineHistory:
  LineHistory.make(
    line,
    h,
    i,
    [Point{line, LineHistory.count(h)}],
    View.frontier(LineHistory.newest(h)),
    PathContents.Content.merge(
      ~merge_content,
      base,
      View.content(LineHistory.newest(h)),
      PathContents.Content.with_changes(changes, base)
    )
  )

# the history h of the line line after the write i of the changes changes from
# the version whose view is base, if the line has it
def LineHistory.write(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  h: LineHistory,
  i: RequestId,
  base: Maybe<&2, View>,
  changes: List<&2, PathContents.Change>
) -> LineHistory:
  match base:
    case None{}:
      LineHistory.decide(h, i, OutcomeRefused{})
    case Some{v}:
      LineHistory.write.from(~merge_content, line, h, i, View.content(v), changes)

# the history h of the line line after the merge i of the version from, whose
# view is t, from the view b, where shared says whether both sides include the
# base
def LineHistory.merge.shared(
  ~merge_content: PathContents.ContentMergeHook(),
  shared: Bool,
  +line: List<&2, U32>,
  +h: LineHistory,
  i: RequestId,
  from: Point,
  +t: View,
  b: View
) -> LineHistory:
  match shared:
    case True{}:
      LineHistory.make(
        line,
        h,
        i,
        [Point{line, LineHistory.count(h)}, from],
        Frontier.join(View.frontier(t), View.frontier(LineHistory.newest(h))),
        PathContents.Content.merge(
          ~merge_content,
          View.content(b),
          View.content(LineHistory.newest(h)),
          View.content(t)
        )
      )
    case False{}:
      LineHistory.decide(h, i, OutcomeRefused{})

# the history h of the line line after the merge i of the version from from the
# version base, which the lookups theirs and based find
def LineHistory.merge(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  +h: LineHistory,
  i: RequestId,
  from: Point,
  base: Point,
  theirs: PointLookup,
  based: PointLookup
) -> LineHistory:
  match theirs based:
    case PointFound{+t} PointFound{b}:
      LineHistory.merge.shared(
        ~merge_content,
        Frontier.both_include(View.frontier(LineHistory.newest(h)), View.frontier(t), base),
        line,
        h,
        i,
        from,
        t,
        b
      )
    case PointOutside{} _:
      LineHistory.decide(h, i, OutcomeRefused{})
    case _ PointOutside{}:
      LineHistory.decide(h, i, OutcomeRefused{})
    case _ _:
      LineHistory.wait(h)

# the history h of the line line after the move i to the version to, which the
# lookup target finds
def LineHistory.move(
  +line: List<&2, U32>,
  +h: LineHistory,
  i: RequestId,
  to: Point,
  target: PointLookup
) -> LineHistory:
  match target:
    case PointFound{+t}:
      LineHistory.make(
        line,
        h,
        i,
        [Point{line, LineHistory.count(h)}, to],
        Frontier.join(View.frontier(t), View.frontier(LineHistory.newest(h))),
        PathContents.ContentsMerged{View.content(t), []}
      )
    case PointOutside{}:
      LineHistory.decide(h, i, OutcomeRefused{})
    case PointUnknown{}:
      LineHistory.wait(h)

# the history h after the mark i of the name name on version version, where
# taken says whether the name names a version already
def LineHistory.mark.fresh(
  taken: Bool,
  h: LineHistory,
  i: RequestId,
  name: List<&2, U32>,
  version: Nat
) -> LineHistory:
  match taken:
    case True{}:
      LineHistory.decide(h, i, OutcomeStale{})
    case False{}:
      match h:
        case LineHistory{vs, ms, ds, w}:
          LineHistory{
            vs,
            AssociationList.with_entry(~Nat, ms, name, Some{version}),
            Decision{i, OutcomeMarked{}} <> ds,
            w
          }

# the history h after the mark i of the name name on version version, where
# within says whether the history has that version
def LineHistory.mark.within(
  within: Bool,
  +h: LineHistory,
  i: RequestId,
  +name: List<&2, U32>,
  version: Nat
) -> LineHistory:
  match within:
    case True{}:
      LineHistory.mark.fresh(
        Maybe.is_some(
          &2,
          Nat,
          AssociationList.value_of_first_entry_with_key(~Nat, LineHistory.marks(h), name)
        ),
        h,
        i,
        name,
        version
      )
    case False{}:
      LineHistory.decide(h, i, OutcomeRefused{})

# the history h after the mark i of the name name on version version
def LineHistory.mark(
  +h: LineHistory,
  i: RequestId,
  name: List<&2, U32>,
  +version: Nat
) -> LineHistory:
  LineHistory.mark.within(Nat.is_le(version, LineHistory.count(h)), h, i, name, version)

# the history h of the line line after the request r of the id i, which was
# not decided before
def LineHistory.request(
  ~merge_content: PathContents.ContentMergeHook(),
  +line: List<&2, U32>,
  +others: List<&2, KnownView>,
  +h: LineHistory,
  i: RequestId,
  r: BranchRequest
) -> LineHistory:
  match r:
    case RequestWrite{base, changes}:
      LineHistory.write(~merge_content, line, h, i, LineHistory.view_at(h, base), changes)
    case RequestMerge{+from, +base}:
      LineHistory.merge(
        ~merge_content,
        line,
        h,
        i,
        from,
        base,
        LineHistory.lookup(line, others, h, from),
        LineHistory.lookup(line, others, h, base)
      )
    case RequestMove{+to}:
      LineHistory.move(line, h, i, to, LineHistory.lookup(line, others, h, to))
    case RequestMark{name, version}:
      LineHistory.mark(h, i, name, version)

# the history h after the request r of the id i, unless skip: the id was
# decided before
def LineHistory.step.unless(
  ~merge_content: PathContents.ContentMergeHook(),
  skip: Bool,
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  h: LineHistory,
  i: RequestId,
  r: BranchRequest
) -> LineHistory:
  match skip:
    case True{}:
      h
    case False{}:
      LineHistory.request(~merge_content, line, others, h, i, r)

# the history h after the request r of the id i, unless it waits, or the id
# was decided before
def LineHistory.step.when_ready(
  ~merge_content: PathContents.ContentMergeHook(),
  waiting: Bool,
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  +h: LineHistory,
  +i: RequestId,
  r: BranchRequest
) -> LineHistory:
  match waiting:
    case True{}:
      h
    case False{}:
      LineHistory.step.unless(
        ~merge_content,
        Decisions.has(LineHistory.decisions(h), i),
        line,
        others,
        h,
        i,
        r
      )

# the history h of the line line after the decided request d
def LineHistory.step(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  +h: LineHistory,
  d: DecidedRequest
) -> LineHistory:
  match d:
    case DecidedRequest{i, r}:
      LineHistory.step.when_ready(~merge_content, LineHistory.waiting(h), line, others, h, i, r)

# the history h after the decided requests rs, in order
def LineHistory.go(
  ~merge_content: PathContents.ContentMergeHook(),
  rs: List<&2, DecidedRequest>,
  +line: List<&2, U32>,
  +others: List<&2, KnownView>,
  h: LineHistory
) -> LineHistory:
  match rs:
    case Nil{}:
      h
    case Con{d, rest}:
      LineHistory.go(
        ~merge_content,
        rest,
        line,
        others,
        LineHistory.step(~merge_content, line, others, h, d)
      )

# the history of the line line after its decided requests rs, in order, where
# others are the views of other lines that the node holds and merge_content

# merges contents in their reader
def LineHistory.of(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  rs: List<&2, DecidedRequest>
) -> LineHistory:
  LineHistory.go(~merge_content, rs, line, others, LineHistory.empty())

# Status
# ------

# what a writer is told of a request: not decided yet, or decided but waiting
# for data (Pending); made a version, or set a mark, with no conflict left
# (Written); made a version with a conflict left (Conflicted); Stale; Refused.
# Stale and Refused are final
type RequestStatus is Data:
  StatusPending{}
  StatusWritten{}
  StatusConflicted{}
  StatusStale{}
  StatusRefused{}

# found, or one of the versions vs holds the path p without a conflict
def Versions.resolve.go(vs: List<&2, Version>, +p: List<&2, U32>, found: Bool) -> Bool:
  match vs:
    case Nil{}:
      found
    case Con{v, rest}:
      match found:
        case True{}:
          True{}
        case False{}:
          Versions.resolve.go(
            rest,
            p,
            Bool.not(
              PathContents.PathEntry.is_conflict(
                PathContents.Content.entry_at(View.content(Version.view(v)), p)
              )
            )
          )

# ok, and each of the paths cs is held without a conflict by one of the
# versions vs
def Versions.resolve_all.go(cs: List<&2, List<&2, U32>>, +vs: List<&2, Version>, ok: Bool) -> Bool:
  match cs:
    case Nil{}:
      ok
    case Con{p, rest}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Versions.resolve_all.go(rest, vs, Versions.resolve.go(vs, p, False{}))

# the status of a request with the outcome o in the history h
def LineHistory.status.of(+h: LineHistory, o: Maybe<&2, Outcome>) -> RequestStatus:
  match o:
    case None{}:
      StatusPending{}
    case Some{OutcomeMadeVersion{k, cs}}:
      Bool.pick(
        RequestStatus,
        Versions.resolve_all.go(
          cs,
          List.take(&2, Version, LineHistory.versions(h), Nat.sub(LineHistory.count(h), k)),
          True{}
        ),
        StatusWritten{},
        StatusConflicted{}
      )
    case Some{OutcomeMarked{}}:
      StatusWritten{}
    case Some{OutcomeStale{}}:
      StatusStale{}
    case Some{OutcomeRefused{}}:
      StatusRefused{}

# the status of the request i in the history h
def LineHistory.status(+h: LineHistory, i: RequestId) -> RequestStatus:
  LineHistory.status.of(h, Decisions.outcome_of(LineHistory.decisions(h), i))

# the paths that clashed in the version that the outcome o made, if it made one
def Outcome.clashes(o: Maybe<&2, Outcome>) -> List<&2, List<&2, U32>>:
  match o:
    case Some{OutcomeMadeVersion{k, cs}}:
      cs
    case _:
      []

# the paths that clashed in the version that the request i made in the history
# h, if it made one
def LineHistory.clashes(h: LineHistory, i: RequestId) -> List<&2, List<&2, U32>>:
  Outcome.clashes(Decisions.outcome_of(LineHistory.decisions(h), i))

# the status b knows at least what the status a knows: Pending knows least; a
# Conflicted request may become Written; every other status stays
def RequestStatus.Below(a: RequestStatus, b: RequestStatus) -> Type:
  match a b:
    case StatusPending{} _:
      Unit
    case StatusConflicted{} StatusConflicted{}:
      Unit
    case StatusConflicted{} StatusWritten{}:
      Unit
    case StatusWritten{} StatusWritten{}:
      Unit
    case StatusStale{} StatusStale{}:
      Unit
    case StatusRefused{} StatusRefused{}:
      Unit
    case _ _:
      Empty

# Helpers of the laws
# -------------------

# the views others2 know at least what others know: every view of others is in
# others2
def Views.KnowMore(others: List<&2, KnownView>, others2: List<&2, KnownView>) -> Type:
  @p: Point -> @v: View -> {KnownViews.view_of(others, p) == Some{v}: Maybe<&2, View>}
    -> {KnownViews.view_of(others2, p) == Some{v}: Maybe<&2, View>}

# version n of the line l is known, where own says whether l is the line of
# the history: always on its own line (it has it or not), and on another line
# when it is version 0 or others holds its view
def Versions.PointKnown.OnLine(
  own: Bool,
  others: List<&2, KnownView>,
  l: List<&2, U32>,
  n: Nat
) -> Type:
  match own:
    case True{}:
      Unit
    case False{}:
      match n:
        case 0n:
          Unit
        case 1n+m:
          Exists(
            View,
            v => {KnownViews.view_of(others, Point{l, 1n+m}) == Some{v}: Maybe<&2, View>}
          )

# the version p is known to the history of the line line
def Versions.PointKnown(line: List<&2, U32>, others: List<&2, KnownView>, p: Point) -> Type:
  match p:
    case Point{+l, n}:
      Versions.PointKnown.OnLine(WordListSets.same(l, line), others, l, n)

# every version that the request r points at is known
def Versions.RequestPointsKnown(
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  r: BranchRequest
) -> Type:
  match r:
    case RequestMerge{from, base}:
      Versions.PointKnown(line, others, from) & Versions.PointKnown(line, others, base)
    case RequestMove{to}:
      Versions.PointKnown(line, others, to)
    case _:
      Unit

# every version that the requests rs point at is known
def Versions.PointsKnown(
  line: List<&2, U32>,
  others: List<&2, KnownView>,
  rs: List<&2, DecidedRequest>
) -> Type:
  match rs:
    case Nil{}:
      Unit
    case Con{DecidedRequest{i, r}, rest}:
      Versions.RequestPointsKnown(line, others, r) & Versions.PointsKnown(line, others, rest)

# each of the paths cs is held without a conflict by some version of the
# history h after version k
def Versions.Resolved(h: LineHistory, k: Nat, cs: List<&2, List<&2, U32>>) -> Type:
  @p: List<&2, U32> -> {WordListSets.contains(cs, p) == True{}: Bool}
    -> Exists(
      Nat,
      j => {
        Nat.is_lt(k, j) == True{}: Bool
      }
        & (
          {
            Nat.is_le(j, LineHistory.count(h)) == True{}: Bool
          }
            & {
              PathContents.PathEntry.is_conflict(
                PathContents.Content.entry_at(LineHistory.content_at(h, j), p)
              )
                == False{}: Bool
            }
        )
    )

# the history h2 is h with the request i refused, and nothing else
def RequestDoes.Refuse(h: LineHistory, i: RequestId, h2: LineHistory) -> Type:
  {h2 == LineHistory.decide(h, i, OutcomeRefused{}): LineHistory}

# the history h2 is h, waiting, and nothing else
def RequestDoes.Wait(h: LineHistory, h2: LineHistory) -> Type:
  {h2 == LineHistory.wait(h): LineHistory}

# the history h2 is h of the line line after the request i made a version
# from the merge m, with the parents parents, and the frontier frontier with
# itself; or h waiting, when m is unknown
def RequestDoes.Make(
  line: List<&2, U32>,
  h: LineHistory,
  i: RequestId,
  parents: List<&2, Point>,
  frontier: List<&2, +Sigma<List<&2, U32>, _ => Nat>>,
  m: PathContents.ContentsMerge,
  h2: LineHistory
) -> Type:
  match m:
    case PathContents.ContentsMergeUnknown{}:
      RequestDoes.Wait(h, h2)
    case PathContents.ContentsMerged{c, cs}:
      {
        h2
          == LineHistory.add(
            h,
            Version{
              i,
              View{
                c,
                AssociationList.with_entry(~Nat, frontier, line, Some{1n+LineHistory.count(h)})
              },
              parents
            },
            Decision{i, OutcomeMadeVersion{1n+LineHistory.count(h), cs}}
          ): LineHistory
      }

# what the write i of the changes cs from version base does to the history h
# of the line line: refused when the line has no such version, else a version
# from the merge of the changes onto the newest content
def RequestDoes.Write(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  h: LineHistory,
  i: RequestId,
  base: Nat,
  cs: List<&2, PathContents.Change>,
  h2: LineHistory
) -> Type:
  (
    {Nat.is_le(base, LineHistory.count(h)) == False{}: Bool} -> RequestDoes.Refuse(h, i, h2)
  )
    & (
      {
        Nat.is_le(base, LineHistory.count(h)) == True{}: Bool
      } -> RequestDoes.Make(
        line,
        h,
        i,
        [Point{line, LineHistory.count(h)}],
        View.frontier(LineHistory.newest(h)),
        PathContents.Content.merge(
          ~merge_content,
          LineHistory.content_at(h, base),
          View.content(LineHistory.newest(h)),
          PathContents.Content.with_changes(cs, LineHistory.content_at(h, base))
        ),
        h2
      )
    )

# what the merge i of the version from, from the version base, which the
# lookups theirs and based find, does to the history h of the line line
def RequestDoes.Merge(
  ~merge_content: PathContents.ContentMergeHook(),
  line: List<&2, U32>,
  h: LineHistory,
  i: RequestId,
  from: Point,
  base: Point,
  theirs: PointLookup,
  based: PointLookup,
  h2: LineHistory
) -> Type:
  match theirs based:
    case PointFound{t} PointFound{b}:
      (
        {
          Frontier.both_include(
            View.frontier(LineHistory.newest(h)),
            View.frontier(t),
            base
          )
            == False{}: Bool
        } -> RequestDoes.Refuse(h, i, h2)
      )
        & (
          {
            Frontier.both_include(
              View.frontier(LineHistory.newest(h)),
              View.frontier(t),
              base
            )
              == True{}: Bool
          } -> RequestDoes.Make(
            line,
            h,
            i,
            [Point{line, LineHistory.count(h)}, from],
            Frontier.join(View.frontier(t), View.frontier(LineHistory.newest(h))),
            PathContents.Content.merge(
              ~merge_content,
              View.content(b),
              View.content(LineHistory.newest(h)),
              View.content(t)
            ),
            h2
          )
        )
    case PointOutside{} _:
      RequestDoes.Refuse(h, i, h2)
    case _ PointOutside{}:
      RequestDoes.Refuse(h, i, h2)
    case _ _:
      RequestDoes.Wait(h, h2)

# what the move i to the version to, which the lookup target finds, does to the
# history h of the line line
def RequestDoes.Move(
  +line: List<&2, U32>,
  +h: LineHistory,
  i: RequestId,
  to: Point,
  target: PointLookup,
  h2: LineHistory
) -> Type:
  match target:
    case PointFound{+t}:
      RequestDoes.Make(
        line,
        h,
        i,
        [Point{line, LineHistory.count(h)}, to],
        Frontier.join(View.frontier(t), View.frontier(LineHistory.newest(h))),
        PathContents.ContentsMerged{View.content(t), []},
        h2
      )
    case PointOutside{}:
      RequestDoes.Refuse(h, i, h2)
    case PointUnknown{}:
      RequestDoes.Wait(h, h2)

# what the mark i of the name name on version version does to the history h:
# refused when the line has no such version, Stale when the name names a
# version already, else the name names the version
def RequestDoes.Mark(
  h: LineHistory,
  i: RequestId,
  name: List<&2, U32>,
  version: Nat,
  h2: LineHistory
) -> Type:
  (
    {Nat.is_le(version, LineHistory.count(h)) == False{}: Bool} -> RequestDoes.Refuse(h, i, h2)
  )
    & (
      {
        Nat.is_le(version, LineHistory.count(h)) == True{}: Bool
      } -> (
        {
          Maybe.is_some(
            &2,
            Nat,
            AssociationList.value_of_first_entry_with_key(~Nat, LineHistory.marks(h), name)
          )
            == True{}: Bool
        } -> {h2 == LineHistory.decide(h, i, OutcomeStale{}): LineHistory}
      )
        & (
          {
            Maybe.is_some(
              &2,
              Nat,
              AssociationList.value_of_first_entry_with_key(~Nat, LineHistory.marks(h), name)
            )
              == False{}: Bool
          } -> {
            LineHistory.status(h2, i) == StatusWritten{}: RequestStatus
          }
            & (
              {
                LineHistory.versions(h2) == LineHistory.versions(h): List<&2, Version>
              }
                & (
                  {
                    LineHistory.waiting(h2) == LineHistory.waiting(h): Bool
                  }
                    & {
                      LineHistory.marks(
                        h2
                      )
                        == AssociationList.with_entry(
                          ~Nat,
                          LineHistory.marks(h),
                          name,
                          Some{version}
                        ): List<&2, +Sigma<List<&2, U32>, _ => Nat>>
                    }
                )
            )
        )
    )

# what the request r of the id i, not decided before, does to the history h of
# the line line, which does not wait, giving h2
def RequestDoes(
  ~merge_content: PathContents.ContentMergeHook(),
  +line: List<&2, U32>,
  +others: List<&2, KnownView>,
  +h: LineHistory,
  i: RequestId,
  r: BranchRequest,
  h2: LineHistory
) -> Type:
  match r:
    case RequestWrite{base, cs}:
      RequestDoes.Write(~merge_content, line, h, i, base, cs, h2)
    case RequestMerge{+from, +base}:
      RequestDoes.Merge(
        ~merge_content,
        line,
        h,
        i,
        from,
        base,
        LineHistory.lookup(line, others, h, from),
        LineHistory.lookup(line, others, h, base),
        h2
      )
    case RequestMove{+to}:
      RequestDoes.Move(line, h, i, to, LineHistory.lookup(line, others, h, to), h2)
    case RequestMark{name, version}:
      RequestDoes.Mark(h, i, name, version, h2)

# Laws
# ----

# Means: with more decided requests, and a content merge hook and views of
# other lines that know at least as much, a line's history only grows: its
# versions are those it had, with new ones after them; a mark keeps its
# version; and the status of each request only moves forward (Pending to any
# status, Conflicted to Written; Written, Stale and Refused stay).
# For free: history is never rewritten; a version, once known, never changes;
# marks name their versions for good; Stale and Refused are final; a node that
# learns more never takes back an answer, so known answers can be cached.
# For the goal: Branch (history only grows at its end, marks for good),
# Version (never changed afterwards), Writer (Stale and Refused are final),
# Behavior 2 and Cost 2.
# Example: a history with 3 versions, given 2 more decided writes and the parts
# that it waited for, has 5 versions whose first 3 are the same.
law Versions.more_data_only_adds:
  for ~merge_content: PathContents.ContentMergeHook()
  for ~merge_content2: PathContents.ContentMergeHook()
  for line: List<&2, U32>
  for others: List<&2, KnownView>
  for others2: List<&2, KnownView>
  for rs: List<&2, DecidedRequest>
  for more: List<&2, DecidedRequest>
  PathContents.ContentMerge.KnowsMore(~merge_content, ~merge_content2)
    -> Views.KnowMore(others, others2)
    -> Exists(
      List<&2, Version>,
      added => {
        LineHistory.versions(
          LineHistory.of(~merge_content2, line, others2, List.append(&2, DecidedRequest, rs, more))
        )
          == List.append(
            &2,
            Version,
            added,
            LineHistory.versions(LineHistory.of(~merge_content, line, others, rs))
          ): List<&2, Version>
      }
    )
      & (
        (
          @name: List<
            &2,
            U32> -> @v: Nat -> {
            AssociationList.value_of_first_entry_with_key(
              ~Nat,
              LineHistory.marks(LineHistory.of(~merge_content, line, others, rs)),
              name
            )
              == Some{v}: Maybe<&2, Nat>
          } -> {
            AssociationList.value_of_first_entry_with_key(
              ~Nat,
              LineHistory.marks(
                LineHistory.of(
                  ~merge_content2,
                  line,
                  others2,
                  List.append(&2, DecidedRequest, rs, more)
                )
              ),
              name
            )
              == Some{v}: Maybe<&2, Nat>
          }
        )
          & (
            @i: RequestId -> RequestStatus.Below(
              LineHistory.status(LineHistory.of(~merge_content, line, others, rs), i),
              LineHistory.status(
                LineHistory.of(
                  ~merge_content2,
                  line,
                  others2,
                  List.append(&2, DecidedRequest, rs, more)
                ),
                i
              )
            )
          )
      )

# Means: a decided request changes nothing when the history waits or its id
# was decided before, whatever it asks. Otherwise it does what it asks. A
# write from a version that the line has makes a version whose content is the
# merge of the writer's changes (onto the version it saw) with the newest
# content, and whose parent is the newest version. A merge makes a version from
# the merge of the version it brings in with the newest content, from a base
# that both include, with both as parents; a move makes a version equal to its
# target, with both as parents. Either waits, changing nothing else, when data
# is unknown, and is refused when it names a version that its line does not
# have, or a base that a side does not include. Each version is named by its
# request, numbered after the newest, and includes itself and all that its
# parents include. A mark names a version of the line, or is Stale when its
# name names one already. Nothing else changes.
# For free: a request counts once: it makes at most one version and gets one
# outcome, however often and wherever it is sent, and a second request that
# reuses an id is ignored; a history that waits keeps its later requests
# Pending, in order; two writers who change different paths, or different
# items of one path, from one version both get their change; a writer who
# wrote from an old version never undoes a change made since; a merge's base
# is a version that both sides come from.
# For the goal: Writer and Behavior 4 (a request counts once; Written,
# Conflicted, Stale, Refused), Branch (moves record a new version equal to the
# target, merges, marks), Version (the whole content after one decided change,
# named by its writer and request id).
# Example: version 3 of main has a.txt "x"; a write of a.txt "y" from version 3
# makes version 4 with a.txt "y", whose parent is version 3; the same write,
# decided again in a later slot, changes nothing.
law Versions.each_request_does_what_it_asks:
  for ~merge_content: PathContents.ContentMergeHook()
  for line: List<&2, U32>
  for others: List<&2, KnownView>
  for rs: List<&2, DecidedRequest>
  for i: RequestId
  for r: BranchRequest
  (
    {
      LineHistory.waiting(LineHistory.of(~merge_content, line, others, rs)) == True{}: Bool
    } -> {
      LineHistory.of(
        ~merge_content,
        line,
        others,
        List.append(&2, DecidedRequest, rs, [DecidedRequest{i, r}])
      )
        == LineHistory.of(~merge_content, line, others, rs): LineHistory
    }
  )
    & (
      (
        {
          Decisions.has(
            LineHistory.decisions(LineHistory.of(~merge_content, line, others, rs)),
            i
          )
            == True{}: Bool
        } -> {
          LineHistory.of(
            ~merge_content,
            line,
            others,
            List.append(&2, DecidedRequest, rs, [DecidedRequest{i, r}])
          )
            == LineHistory.of(~merge_content, line, others, rs): LineHistory
        }
      )
        & (
          {
            LineHistory.waiting(LineHistory.of(~merge_content, line, others, rs)) == False{}: Bool
          } -> {
            Decisions.has(
              LineHistory.decisions(LineHistory.of(~merge_content, line, others, rs)),
              i
            )
              == False{}: Bool
          } -> RequestDoes(
            ~merge_content,
            line,
            others,
            LineHistory.of(~merge_content, line, others, rs),
            i,
            r,
            LineHistory.of(
              ~merge_content,
              line,
              others,
              List.append(&2, DecidedRequest, rs, [DecidedRequest{i, r}])
            )
          )
        )
    )

# Means: a request that made a version with clashes is Written exactly when
# each path that clashed is held without a conflict by some later version of
# the line, and Conflicted until then.
# For free: a conflict is resolved by writing the path; a merge with no clash
# is Written at once; a request is never Conflicted over a path it did not
# clash on.
# For the goal: the merge turns Written once each clashing resource is
# resolved (Branch).
# Example: a merge that made version 5 with a.txt in conflict is Conflicted,
# and Written once version 7 holds a.txt without a conflict.
law Versions.conflicted_until_resolved:
  for ~merge_content: PathContents.ContentMergeHook()
  for line: List<&2, U32>
  for others: List<&2, KnownView>
  for rs: List<&2, DecidedRequest>
  for i: RequestId
  for k: Nat
  for cs: List<&2, List<&2, U32>>
  {
    Decisions.outcome_of(
      LineHistory.decisions(LineHistory.of(~merge_content, line, others, rs)),
      i
    )
      == Some{OutcomeMadeVersion{k, cs}}: Maybe<&2, Outcome>
  }
    -> (
      {
        LineHistory.status(
          LineHistory.of(~merge_content, line, others, rs),
          i
        )
          == StatusWritten{}: RequestStatus
      } -> Versions.Resolved(LineHistory.of(~merge_content, line, others, rs), k, cs)
    )
      & (
        (
          Versions.Resolved(
            LineHistory.of(~merge_content, line, others, rs),
            k,
            cs
          ) -> {
            LineHistory.status(
              LineHistory.of(~merge_content, line, others, rs),
              i
            )
              == StatusWritten{}: RequestStatus
          }
        )
          & (
            (
              {
                LineHistory.status(
                  LineHistory.of(~merge_content, line, others, rs),
                  i
                )
                  == StatusWritten{}: RequestStatus
              } -> Empty
            ) -> {
              LineHistory.status(
                LineHistory.of(~merge_content, line, others, rs),
                i
              )
                == StatusConflicted{}: RequestStatus
            }
          )
      )

# Means: a history never waits when the content merge hook always knows and
# every version of another line that the requests point at is held.
# For free: with Unknown as the only other way, a node that holds the parts and
# the other lines' versions that a line needs knows every status and version
# of that line.
# For the goal: an answer is Unknown only while data is missing, never for
# good (Behavior 2: each monotone query states when it must know).
# Example: a node that holds every part and every version of dev knows the
# merge of dev into main.
law Versions.knows_when_all_is_held:
  for ~merge_content: PathContents.ContentMergeHook()
  for line: List<&2, U32>
  for others: List<&2, KnownView>
  for rs: List<&2, DecidedRequest>
  PathContents.ContentMerge.AlwaysKnows(~merge_content)
    -> Versions.PointsKnown(line, others, rs)
    -> {LineHistory.waiting(LineHistory.of(~merge_content, line, others, rs)) == False{}: Bool}
