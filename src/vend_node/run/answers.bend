import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../groups.bend as Groups
import ../shared/format.bend as Formats
import ../shared/lists.bend as Lists
import ../spec.bend as Spec
import ../types.bend as Types
import ./content.bend as Contents
import ./facts.bend as Facts
import ./files.bend as Files
import ./known.bend as Known
import ./lines.bend as Lines
import ./rounds.bend as Rounds

# Answers
# -------
# What a node replies to a question: a read of the versions that its facts
# decide. A reply is nothing (Unknown) while the facts do not decide it.

# the request of the entry e
def Entry.request(e: Types.Entry) -> Spec.Request:
  Lines.Ask.request(Lines.Entry.ask(e))

# a merge and one of its paths
type Clash is Data:
  Clash{merge: Ledgers.Id, path: String}

# the entry of the version m, if any, among the versions vs
def Versions.find.at(+vs: List<&2, Types.Entry>, m: Maybe<&2, Nat>) -> Maybe<&2, Known.Found>:
  match m:
    case None{}:
      None{}
    case Some{+k}:
      Maybe.map(
        &2,
        Types.Entry,
        Known.Found,
        e => Known.Found{k, e},
        List.get(&2, Types.Entry, vs, k)
      )

# the entry of the id i among the versions vs, and its version
def Versions.find(+vs: List<&2, Types.Entry>, i: Ledgers.Id) -> Maybe<&2, Known.Found>:
  Versions.find.at(vs, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i))

# Status
# ------

# the request r resolves the path p of the merge i
def Request.resolves(i: Ledgers.Id, p: String, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Resolve{m, q, w}:
      Bool.and(Ledgers.Id.is_eq(m, i), String.eq(q, p))
    case _:
      False{}

# the entry e resolves the path p of the merge i
def Entry.resolves(g: Clash, e: Types.Entry) -> Bool:
  match g:
    case Clash{i, p}:
      Request.resolves(i, p, Entry.request(e))

# a merge and the versions of its line
type Resolved is Data:
  Resolved{versions: List<&2, Types.Entry>, merge: Ledgers.Id}

# a version of g resolves the path p of the merge of g
def Resolved.has(g: Resolved, p: String) -> Bool:
  match g:
    case Resolved{vs, i}:
      Shared.List.some(~Types.Entry, ~Clash, ~Entry.resolves, vs, Clash{i, p})

# the status of the merge i, with the paths m that clash in it, if the node
# knows them: Written once each is resolved
def Status.merge(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  m: Maybe<&2, List<&2, String>>
) -> Spec.Status:
  match m:
    case None{}:
      Spec.Status.Conflicted{i}
    case Some{ps}:
      Bool.pick(
        Spec.Status,
        Shared.List.holds(~String, ~Resolved, ~Resolved.has, ps, Resolved{vs, i}),
        Spec.Status.Written{},
        Spec.Status.Conflicted{i}
      )

# the request r sets the mark m
def Request.marks(m: String, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Mark{b, name, v}:
      String.eq(name, m)
    case _:
      False{}

# the entry e sets the mark m
def Entry.marks(m: String, e: Types.Entry) -> Bool:
  Request.marks(m, Entry.request(e))

# the status of the mark m set by version k: Written when no older version
# set the mark, since a mark names its version for good
def Status.mark(vs: List<&2, Types.Entry>, m: String, k: Nat) -> Spec.Status:
  Bool.pick(
    Spec.Status,
    Shared.Maybe.is_eq(
      ~Nat,
      ~Nat.is_eq,
      Lists.List.index(~Types.Entry, ~String, ~Entry.marks, vs, m),
      Some{k}
    ),
    Spec.Status.Written{},
    Spec.Status.Stale{}
  )

# Merges
# ------

# the paths that clash in a merge that fits, of the contents base, ours and
# theirs, when the node holds them
def Clashes.at(
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> Maybe<&2, List<&2, String>>:
  match fits base ours theirs:
    case True{} Some{b} Some{o} Some{t}:
      Some{Contents.Merge.clashes(b, o, t)}
    case _ _ _ _:
      None{}

# the paths that clash in a merge, as Clashes.at gives them, when theirs is
# base with the writes ws
def Clashes.at.few(
  ws: List<&2, Contents.Write>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> Maybe<&2, List<&2, String>>:
  match fits base ours theirs:
    case True{} Some{b} Some{o} Some{t}:
      Some{Contents.Merge.clashes.few(b, o, t, ws)}
    case _ _ _ _:
      None{}

# the paths that clash in a merge, as Clashes.at gives them: when the writes
# h that make theirs from base are known, only their paths are merged
def Clashes.quick(
  h: Maybe<&2, List<&2, Contents.Write>>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> Maybe<&2, List<&2, String>>:
  match h:
    case None{}:
      Clashes.at(fits, base, ours, theirs)
    case Some{ws}:
      Clashes.at.few(ws, fits, base, ours, theirs)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- for an entry that is no merge, Merge.fits finds no base and stops
# the paths that clash in the merge e, version k of the line c
def Clashes.of(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> Maybe<&2, List<&2, String>>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      +j = j
      +a = Contents.Entry.based(c, Some{e})
      +t = Contents.Entry.taken(c, Some{e})
      Clashes.quick(
        Contents.Merge.hint.seen(Known.Known.seen(kn, Spec.Point.line(t)), t, a),
        Bool.and(Contents.Request.is_merge(Entry.request(e)), Contents.Merge.fits(kn, s, c, j, e)),
        Contents.Content.of(kn, s, Spec.Point.line(a), Spec.Point.n(a)),
        Contents.Content.of(kn, s, c, j),
        Contents.Content.of(kn, s, Spec.Point.line(t), Spec.Point.n(t))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the base of the merge e, version k of the line c, when its ways lead to it
def Base.of(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> Maybe<&2, Spec.Point>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      Shared.Maybe.when(
        Spec.Point,
        Contents.Merge.fits(kn, s, c, j, e),
        u => Contents.Entry.base(e)
      )

# the status of the request r of the id i, version k among vs, with the
# paths cs that clash in it if it is a merge and the node knows them
def Status.by(
  +vs: List<&2, Types.Entry>,
  k: Nat,
  +i: Ledgers.Id,
  r: Spec.Request,
  cs: Maybe<&2, List<&2, String>>
) -> Spec.Status:
  match r:
    case Spec.Request.Merge{f, x}:
      Status.merge(vs, i, cs)
    case Spec.Request.Mark{b, m, v}:
      Status.mark(vs, m, k)
    case _:
      Spec.Status.Written{}

# the status of the request r, version k of the line c
def Status.of(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +e: Types.Entry
) -> Spec.Status:
  Status.by(vs, k, Lines.Entry.id(e), Entry.request(e), Clashes.of(kn, s, c, k, e))

# The rule of a version
# ---------------------

# Line.before, once the versions m of the line are known
def Line.before.of(
  +j: Nat,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, List<&2, Types.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{+vs}:
      Shared.Maybe.when(
        List<&2, Types.Entry>,
        Nat.is_lt(j, List.length(&2, Types.Entry, vs)),
        u => Some{List.take(&2, Types.Entry, vs, 1n+j)}
      )

# the versions of the line c before its version 1+j, when the line has that
# many, or one less (the version that comes next)
def Line.before(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> Maybe<&2, List<&2, Types.Entry>>:
  Line.before.of(j, Known.Known.versions(kn, s, c))

# Rule.for, once the versions m before the version are known
def Rule.for.of(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      Known.Known.rule(kn, s, c, vs)

# the rule of version k of the line c: of the versions before it
def Rule.for(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> Maybe<&2, Lines.Rule>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      Rule.for.of(kn, s, c, Line.before(kn, s, c, j))

# the era of version k of the line c
def Era.for(+kn: Known.Known(), +s: Facts.Plain(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, Nat>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      Maybe.map(
        &2,
        List<&2, Types.Entry>,
        Nat,
        vs => Lines.Line.era(c, vs),
        Line.before(kn, s, c, j)
      )

# the reply of the names of the nodes of the rule u, when the store named its
# owner group
def Rule.group(u: Lines.Rule) -> Maybe<&2, Spec.Reply>:
  match u:
    case Lines.Rule{None{}, ns}:
      None{}
    case Lines.Rule{Some{g}, ns}:
      Some{Spec.Reply.Names{ns}}

# the reply of the name of the owner group of the rule u
def Rule.owner(u: Lines.Rule) -> Maybe<&2, Spec.Reply>:
  match u:
    case Lines.Rule{None{}, ns}:
      None{}
    case Lines.Rule{Some{g}, ns}:
      Some{Spec.Reply.Name{g}}

# the first nodes of the rule u that are more than half of it, when the facts
# hold a sound vote of each of them, in one round, for the entry e of the
# line c
def Rule.voters(
  +s: Facts.Plain(),
  c: Ledgers.Line,
  e: Types.Entry,
  u: Lines.Rule
) -> Maybe<&2, Spec.Reply>:
  match e u:
    case Types.Entry{pk, +k} Lines.Rule{g, +ns}:
      +os = Lists.List.lead(String, ns)
      Shared.Maybe.when(
        Spec.Reply,
        Shared.Bool.when(
          Bool,
          Bool.not(List.is_empty(&2, String, ns)),
          un => Rounds.Slot.backed(Rounds.Slot.ballots(Facts.Facts.list(s), c, k), ns, k, os, pk),
          un => False{}
        ),
        u2 => Some{Spec.Reply.Names{os}}
      )

# the nodes whose votes decided version k of the line c, once its entry m and
# its rule u are known
def Owners.of(
  +s: Facts.Plain(),
  c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>,
  u: Maybe<&2, Lines.Rule>
) -> Maybe<&2, Spec.Reply>:
  match m u:
    case Some{e} Some{rule}:
      Rule.voters(s, c, e, rule)
    case _ _:
      None{}

# Groups
# ------

# Store.read, once the versions v of the store are known
def Store.read.of(
  -A: Data,
  m: Nat,
  f: List<&2, Types.Entry> -> Maybe<&2, A>,
  v: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, A>:
  match v:
    case None{}:
      None{}
    case Some{+R}:
      Shared.Maybe.when(A, Nat.is_lt(m, List.length(&2, Types.Entry, R)), u => f(R))

# a read of the groups of the store h at its version m, when the node holds
# that version
def Store.read(
  -A: Data,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +h: Hashes.Hash,
  +m: Nat,
  f: List<&2, Types.Entry> -> Maybe<&2, A>
) -> Maybe<&2, A>:
  Store.read.of(A, m, f, Known.Known.store(kn, s, h))

# What a writer is told
# ---------------------

# Reach.imports, once the words m of the resource are known
def Reach.imports.of(
  p: String,
  bs: List<&2, String>,
  m: Maybe<&2, List<&2, U32>>
) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{ws}:
      Formats.Format.imports(p, ws, bs)

# the paths that the resource at the path p of the content b imports, in the
# build of the conditions bs
def Reach.imports(+b: Files.Files(), bs: List<&2, String>, +p: String) -> List<&2, String>:
  Reach.imports.of(p, bs, Files.Files.get(b, p))

# a content, the conditions of a build, and the paths of the content that
# hold words: the graph of its imports
type Reached is Data:
  Reached{content: Files.Files(), build: List<&2, String>, paths: List<&2, String>}

# the imports of the path p in the content b, when p holds words (hit)
def Reached.succ.if(
  hit: Bool,
  +b: Files.Files(),
  bs: List<&2, String>,
  +p: String
) -> List<&2, String>:
  match hit:
    case False{}:
      []
    case True{}:
      Reach.imports(b, bs, p)

# the imports of the path p in the content b, when p is one of the paths ps
def Reached.succ.of(
  +b: Files.Files(),
  bs: List<&2, String>,
  ps: List<&2, String>,
  +p: String
) -> List<&2, String>:
  Reached.succ.if(List.contains(~String, ~String.eq, ps, p), b, bs, p)

# the paths that the path p leads to in g: its imports
def Reached.succ(g: Reached, p: String) -> List<&2, String>:
  match g:
    case Reached{b, bs, ps}:
      Reached.succ.of(b, bs, ps, p)

# the paths that lead to others in g: those that hold words
def Reached.nodes(g: Reached) -> List<&2, String>:
  match g:
    case Reached{b, bs, ps}:
      ps

# the paths us and those that they reach through imports in the content b, in
# the build of the conditions bs, each once
def Reach.of(+b: Files.Files(), bs: List<&2, String>, us: List<&2, String>) -> List<&2, String>:
  Groups.Closure.of(
    ~String,
    ~Reached,
    ~String.eq,
    ~Reached.succ,
    ~Reached.nodes,
    Reached{b, bs, Files.Files.paths(b)},
    us
  )

# two contents
type Delta is Data:
  Delta{old: Files.Files(), new: Files.Files()}

# the words at the path p differ in the two contents of g
def Delta.differ(g: Delta, p: String) -> Bool:
  match g:
    case Delta{a, b}:
      +p = p
      Bool.not(
        Shared.Maybe.is_eq(
          ~List<&2, U32>,
          ~Facts.Words.is_eq,
          Files.Files.get(a, p),
          Files.Files.get(b, p)
        )
      )

# the paths ps whose words differ in the two contents of g
def Delta.changed(+g: Delta, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.filter.put(String, p, Delta.changed(g, rest), Delta.differ(g, p))

# the paths that changed between two contents, if the node holds both, among
# us and those that us reaches in the newer
def Affects.of(
  old: Maybe<&2, Files.Files()>,
  new: Maybe<&2, Files.Files()>,
  us: List<&2, String>,
  bs: List<&2, String>
) -> Maybe<&2, Spec.Reply>:
  match old new:
    case Some{a} Some{+b}:
      Some{Spec.Reply.Names{Delta.changed(Delta{a, b}, Reach.of(b, bs, us))}}
    case _ _:
      None{}

# The answer
# ----------

# the reply of the id of the entry m, if any
def Reply.id(m: Maybe<&2, Types.Entry>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Spec.Reply.Id{Lines.Entry.id(e)}}

# the reply of the request of the found entry m, if any
def Reply.ask(m: Maybe<&2, Known.Found>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{Known.Found{k, e}}:
      Some{Spec.Reply.Ask{Entry.request(e)}}

# the reply of the count of the versions m, if known
def Reply.count(m: Maybe<&2, List<&2, Types.Entry>>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      Some{Spec.Reply.Number{List.length(&2, Types.Entry, vs)}}

# the reply of the names m, if known
def Reply.names(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{ns}:
      Some{Spec.Reply.Names{ns}}

# the reply of the number m, if known
def Reply.number(m: Maybe<&2, Nat>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{Spec.Reply.Number{k}}

# the reply of the point m, if known
def Reply.point(m: Maybe<&2, Spec.Point>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Spec.Reply.Point{x}}

# the reply of the hash of the content m, if known
def Reply.hash(m: Maybe<&2, Files.Files()>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Spec.Reply.Hash{Files.Files.hash(t)}}

# the reply of whether a name is a group, if known
def Reply.yes(m: Maybe<&2, Bool>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{y}:
      Some{Spec.Reply.Yes{y}}

# the reply of the parents of version k of the line c, the entry m if known
def Reply.parents(c: Ledgers.Line, k: Nat, m: Maybe<&2, Types.Entry>) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Spec.Reply.Points{Contents.Entry.parents(c, k, e)}}

# what the found entry m of the line c, if any, answers by f
def Found.then(
  -A: Data,
  m: Maybe<&2, Known.Found>,
  f: Nat -> Types.Entry -> Maybe<&2, A>
) -> Maybe<&2, A>:
  match m:
    case None{}:
      None{}
    case Some{Known.Found{k, e}}:
      f(k)(e)

# Line.find, once the versions m of the line are known
def Line.find.of(i: Ledgers.Id, m: Maybe<&2, List<&2, Types.Entry>>) -> Maybe<&2, Known.Found>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      Versions.find(vs, i)

# the entry of the id i in the line c, and its version: read from the
# versions x of c by id, if known
def Line.find.by(
  x: Maybe<&2, Known.Ids>,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  i: Ledgers.Id
) -> Maybe<&2, Known.Found>:
  match x:
    case None{}:
      Line.find.of(i, Known.Known.versions(kn, s, c))
    case Some{ids}:
      Known.Ids.find(ids, i)

# the entry of the id i in the line c, and its version
def Line.find(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  i: Ledgers.Id
) -> Maybe<&2, Known.Found>:
  Line.find.by(Known.Known.ids(kn, c), kn, s, c, i)

# the reply of the status of the found entry m of the line c, with the
# versions v of the line
def Reply.status(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, Known.Found>
) -> Maybe<&2, Spec.Reply>:
  match v m:
    case Some{vs} Some{Known.Found{k, e}}:
      Some{Spec.Reply.Status{Status.of(kn, s, c, vs, k, e)}}
    case _ _:
      None{}

# the status of the request r of the id i, version k among the versions rev,
# the newest first: the versions are read only for a merge and a mark
def Status.by.seen(
  rev: List<&2, Types.Entry>,
  k: Nat,
  +i: Ledgers.Id,
  r: Spec.Request,
  cs: Maybe<&2, List<&2, String>>
) -> Spec.Status:
  match r:
    case Spec.Request.Merge{f, x}:
      Status.merge(List.reverse(&2, Types.Entry, rev), i, cs)
    case Spec.Request.Mark{b, m, v}:
      Status.mark(List.reverse(&2, Types.Entry, rev), m, k)
    case _:
      Spec.Status.Written{}

# the reply of the status of the found entry m of the line c, with the
# versions rev of the line, the newest first
def Reply.status.seen(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  rev: List<&2, Types.Entry>,
  m: Maybe<&2, Known.Found>
) -> Maybe<&2, Spec.Reply>:
  match m:
    case None{}:
      None{}
    case Some{Known.Found{+k, +e}}:
      Some{
        Spec.Reply.Status{
          Status.by.seen(rev, k, Lines.Entry.id(e), Entry.request(e), Clashes.of(kn, s, c, k, e))
        }
      }

# the reply of the status of the found entry m of the line c: read from the
# state x that the table kn keeps for c, if any
def Reply.status.by(
  x: Maybe<&2, Known.Seen>,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, Known.Found>
) -> Maybe<&2, Spec.Reply>:
  match x:
    case None{}:
      Reply.status(kn, s, c, Known.Known.versions(kn, s, c), m)
    case Some{Known.Seen{rev, n, j}}:
      Reply.status.seen(kn, s, c, rev, m)

# the version that the mark r names
def Request.marked(r: Spec.Request) -> Maybe<&2, Nat>:
  match r:
    case Spec.Request.Mark{b, m, v}:
      Some{v}
    case _:
      None{}

# the version that the mark of the entry m, if any, names
def Mark.in(m: Maybe<&2, Types.Entry>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Request.marked(Entry.request(e))

# the version that the mark set by version j, if any, names
def Mark.at(vs: List<&2, Types.Entry>, j: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match j:
    case None{}:
      None{}
    case Some{k}:
      Mark.in(List.get(&2, Types.Entry, vs, k))

# the version that the mark m names among the versions v, if known
def Mark.of(m: String, v: Maybe<&2, List<&2, Types.Entry>>) -> Maybe<&2, Nat>:
  match v:
    case None{}:
      None{}
    case Some{+vs}:
      Mark.at(vs, Lists.List.index(~Types.Entry, ~String, ~Entry.marks, vs, m))

# the reply of the count of the versions of the line c: the count that the
# versions x of c by id hold, if known
def Reply.count.by(
  x: Maybe<&2, Known.Ids>,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Maybe<&2, Spec.Reply>:
  match x:
    case None{}:
      Reply.count(Known.Known.versions(kn, s, c))
    case Some{ids}:
      Some{Spec.Reply.Number{Known.Ids.count(ids)}}

# the reply of the facts s to the question q
def Answer.of(+kn: Known.Known(), +s: Facts.Plain(), q: Spec.Question) -> Maybe<&2, Spec.Reply>:
  match q:
    case Spec.Question.Status{+c, i}:
      Reply.status.by(Known.Known.seen(kn, c), kn, s, c, Line.find(kn, s, c, i))
    case Spec.Question.Request{c, i}:
      Reply.ask(Line.find(kn, s, c, i))
    case Spec.Question.Version{c, k}:
      Reply.id(Known.Known.at(kn, s, c, k))
    case Spec.Question.Content{c, k}:
      Reply.hash(Contents.Content.of(kn, s, c, k))
    case Spec.Question.Group{c, k}:
      Maybe.bind(&2, Lines.Rule, Spec.Reply, Rule.for(kn, s, c, k), Rule.group)
    case Spec.Question.Owners{+c, +k}:
      Owners.of(s, c, Known.Known.at(kn, s, c, k), Rule.for(kn, s, c, k))
    case Spec.Question.Members{+h, g, +m}:
      Reply.names(Store.read(List<&2, String>, kn, s, h, m, R => Groups.Groups.members(R, h, g, m)))
    case Spec.Question.Nodes{+h, g, +m}:
      Reply.names(Store.read(List<&2, String>, kn, s, h, m, R => Groups.Groups.nodes(R, h, g, m)))
    case Spec.Question.IsGroup{+h, g, +m}:
      Reply.yes(Store.read(Bool, kn, s, h, m, R => Groups.Groups.is_group(R, h, g, m)))
    case Spec.Question.Mark{c, m}:
      Reply.number(Mark.of(m, Known.Known.versions(kn, s, c)))
    case Spec.Question.Count{+c}:
      Reply.count.by(Known.Known.ids(kn, c), kn, s, c)
    case Spec.Question.Clashes{+c, i}:
      Reply.names(
        Found.then(List<&2, String>, Line.find(kn, s, c, i), k => e => Clashes.of(kn, s, c, k, e))
      )
    case Spec.Question.Affects{+c, a, b, us, bs}:
      Affects.of(Contents.Content.of(kn, s, c, a), Contents.Content.of(kn, s, c, b), us, bs)
    case Spec.Question.Parents{+c, +k}:
      Reply.parents(c, k, Known.Known.at(kn, s, c, k))
    case Spec.Question.Base{+c, i}:
      Reply.point(Found.then(Spec.Point, Line.find(kn, s, c, i), k => e => Base.of(kn, s, c, k, e)))
    case Spec.Question.Owner{c, k}:
      Maybe.bind(&2, Lines.Rule, Spec.Reply, Rule.for(kn, s, c, k), Rule.owner)
    case Spec.Question.Era{c, k}:
      Reply.number(Era.for(kn, s, c, k))

# Views
# -----

# the request r writes the path p of the branch b
def Request.writes(b: Ledgers.Line, p: String, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Write{c, q, ws}:
      Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p))
    case _:
      False{}

# the ask a is a write of the writer w at the path p of the branch b
def Ask.writes(g: Known.Place, a: Types.Ask) -> Bool:
  match g a:
    case Known.Place{w, b, p} Types.Ask{Ledgers.Id{author, name}, k, r}:
      Bool.and(String.eq(author, w), Request.writes(b, p, r))

# the asks among fs that are writes as g says
def Writes.of(fs: List<&2, Types.Fact>, +g: Known.Place) -> List<&2, Types.Ask>:
  match fs:
    case Nil{}:
      []
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Writes.of(rest, g)
    case Con{Types.Fact.Ask{+a}, rest}:
      List.filter.put(Types.Ask, a, Writes.of(rest, g), Ask.writes(g, a))

# the words that the request r writes
def Request.words(r: Spec.Request) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Spec.Request.Write{c, q, ws}:
      ws
    case _:
      None{}

# the words at the path p of the newest of the versions m of the branch b
def View.newest(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      Contents.Content.read(kn, s, b, Nat.sub(List.length(&2, Types.Entry, vs), 1n), p)

# a version of the branch, of the versions m, was made by the ask a
def View.decided(a: Types.Ask, m: Maybe<&2, List<&2, Types.Entry>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{vs}:
      Shared.List.some(~Types.Entry, ~Types.Ask, ~Known.Entry.made_by, vs, a)

# the view of a writer whose last write there is the ask m, if any: its words
# while no version was made by it; else what the newest version holds
def View.slow(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      View.newest(kn, s, b, p, Known.Known.versions(kn, s, b))
    case Some{+a}:
      Shared.Bool.when(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        View.decided(a, Known.Known.versions(kn, s, b)),
        u => View.newest(kn, s, b, p, Known.Known.versions(kn, s, b)),
        u => Some{Request.words(Lines.Ask.request(a))}
      )

# the words at the path p of the newest of the versions x of the branch b
def View.last(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  x: Known.Ids
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Contents.Content.read(kn, s, b, Nat.sub(Known.Ids.count(x), 1n), p)

# View.slow, read from the versions x of the branch b by id
def View.quick(
  +x: Known.Ids,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      View.last(kn, s, b, p, x)
    case Some{+a}:
      Shared.Bool.when(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Known.Ids.made(x, a),
        u => View.last(kn, s, b, p, x),
        u => Some{Request.words(Lines.Ask.request(a))}
      )

# the view of a writer whose last write there is the ask m, if any: read
# from the versions x of the branch b by id, if known
def View.of.by(
  x: Maybe<&2, Known.Ids>,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match x:
    case None{}:
      View.slow(kn, s, b, p, m)
    case Some{ids}:
      View.quick(ids, kn, s, b, p, m)

# the view of a writer whose last write there is the ask m, if any: its words
# while no version was made by it; else what the newest version holds
def View.of(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  View.of.by(Known.Known.ids(kn, b), kn, s, b, p, m)

# the newest write at the place g in the facts s: as the entry m holds it,
# else read from the facts
def View.top(m: Maybe<&2, Known.Kept>, s: Facts.Plain(), +g: Known.Place) -> Maybe<&2, Types.Ask>:
  match m:
    case Some{Known.Open{fs, n, tx, mx}}:
      Known.Tops.get(tx, g)
    case _:
      Lists.List.top(~Types.Ask, ~Facts.Ask.seq, Writes.of(Facts.Facts.list(s), g))

# the words that the writer w reads at the path p of the newest version of
# the branch b, its own writes included
def View.at(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  View.of(kn, s, b, p, View.top(Known.Known.shelf(kn), s, Known.Place{w, b, p}))
