import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./mirror.bend as Mirror
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions

# The laws of an owner group
# --------------------------
# The replies about the groups of a store are reads of the versions of the
# store (groups.bend): each law of the spec about them is a law of those reads.

# what holds of a holds of what equals a
def Own.cast(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b: A}, p: P(a)) -> P(b):
  %e: P(_)
  p

# Replies
# -------

# the names of a reply of names
def Reply.names_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{Spec.Reply.Names{ns}}:
      Some{ns}
    case _:
      None{}

# whether a reply of yes or no says yes
def Reply.yes_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, Bool>:
  match m:
    case Some{Spec.Reply.Yes{y}}:
      Some{y}
    case _:
      None{}

# the number of a reply of a number
def Reply.number_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, Nat>:
  match m:
    case Some{Spec.Reply.Number{k}}:
      Some{k}
    case _:
      None{}

# the name of a reply of a name
def Reply.name_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, String>:
  match m:
    case Some{Spec.Reply.Name{g}}:
      Some{g}
    case _:
      None{}

# the id of a reply of an id
def Reply.id_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, Ledgers.Id>:
  match m:
    case Some{Spec.Reply.Id{i}}:
      Some{i}
    case _:
      None{}

# the request of a reply of a request
def Reply.ask_of(m: Maybe<&2, Spec.Reply>) -> Maybe<&2, Spec.Request>:
  match m:
    case Some{Spec.Reply.Ask{r}}:
      Some{r}
    case _:
      None{}

# a reply of the names ns comes from the names ns
def Reply.names_some(m: Maybe<&2, List<&2, String>>, -ns: List<&2, String>) -> {
  Answers.Reply.names(m) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
} -> {m == Some{ns}: Maybe<&2, List<&2, String>>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{ns}: Maybe<&2, List<&2, String>>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ns}, h)
      )
    case Some{x}:
      h => Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, List<&2, String>>,
        Reply.names_of,
        Some{Spec.Reply.Names{x}},
        Some{Spec.Reply.Names{ns}},
        h
      )

# a reply of yes or no comes from that
def Reply.yes_some(m: Maybe<&2, Bool>, -y: Bool) -> {
  Answers.Reply.yes(m) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
} -> {m == Some{y}: Maybe<&2, Bool>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{y}: Maybe<&2, Bool>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Yes{y}, h)
      )
    case Some{x}:
      h => Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, Bool>,
        Reply.yes_of,
        Some{Spec.Reply.Yes{x}},
        Some{Spec.Reply.Yes{y}},
        h
      )

# a reply of the number k comes from the number k
def Reply.number_some(m: Maybe<&2, Nat>, -k: Nat) -> {
  Answers.Reply.number(m) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
} -> {m == Some{k}: Maybe<&2, Nat>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{k}: Maybe<&2, Nat>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Number{k}, h)
      )
    case Some{x}:
      h => Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, Nat>,
        Reply.number_of,
        Some{Spec.Reply.Number{x}},
        Some{Spec.Reply.Number{k}},
        h
      )

# Reads of a store
# ----------------

# an answer given when b holds is given: b holds, and it is the answer
def When.some(-A: Data, b: Bool, -y: Maybe<&2, A>, -x: A, h: {Shared.Maybe.when(A, b, u => y) == Some{x}: Maybe<&2, A>}) -> {
  b == True{}: Bool
}
  & {y == Some{x}: Maybe<&2, A>}:
  match b:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd({False{} == True{}: Bool} & {y == Some{x}: Maybe<&2, A>}, Shared.Maybe.none_ne_some(A, x, h))

# a read of a store that answers: the store has versions, and the version read
# is one of them
def Read.some(-A: Data, +m: Nat, -f: List<&2, Types.Entry> -> Maybe<&2, A>, v: Maybe<&2, List<&2, Types.Entry>>, -x: A) -> {
  Answers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>
} -> Exists(
  List<&2, Types.Entry>,
  R => {
    v == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & ({Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool} & {f(R) == Some{x}: Maybe<&2, A>})
):
  match v:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          R => {
            None{} == Some{R}: Maybe<&2, List<&2, Types.Entry>>
          }
            & ({Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool} & {f(R) == Some{x}: Maybe<&2, A>})
        ),
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Some{+R}:
      h => (R, ({==}, When.some(A, Nat.is_lt(m, List.length(&2, Types.Entry, R)), f(R), x, h)))

# a read of a store of the versions R that answers: the version read is one of
# R, and the answer is the read of R
def Read.at(
  -A: Data,
  +m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>,
  -v: Maybe<&2, List<&2, Types.Entry>>,
  +R: List<&2, Types.Entry>,
  -x: A,
  ev: {v == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  e: {Answers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>}
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
}
  & {f(R) == Some{x}: Maybe<&2, A>}:
  When.some(
    A,
    Nat.is_lt(m, List.length(&2, Types.Entry, R)),
    f(R),
    x,
    Own.cast(
      Maybe<&2, List<&2, Types.Entry>>,
      w => {Answers.Store.read.of(A, m, f, w) == Some{x}: Maybe<&2, A>},
      v,
      Some{R},
      ev,
      e
    )
  )

# a read of a store of the versions R answers the read of R, when the version
# read is one of R
def Read.make(
  -A: Data,
  -m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>,
  -v: Maybe<&2, List<&2, Types.Entry>>,
  -R: List<&2, Types.Entry>,
  -x: A,
  ev: {v == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
  ef: {f(R) == Some{x}: Maybe<&2, A>}
) -> {Answers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>}:
  %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, v, Some{R}, ev): {Answers.Store.read.of(A, m, f, _) == Some{x}: Maybe<&2, A>}
  %Equal.sym(Bool, Nat.is_lt(m, List.length(&2, Types.Entry, R)), True{}, lt): {Shared.Maybe.when(A, _, u => f(R)) == Some{x}: Maybe<&2, A>}
  ef

# The nodes of a group
# --------------------

# the reply of the nodes of the group g of the store h at its version m, when
# the versions R of the store reach m: the nodes that R gives
def Nodes.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -R: List<&2, Types.Entry>,
  -ns: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
  en: {Groups.Groups.nodes(R, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>}
) -> {Answers.Answer.of(s, Spec.Question.Nodes{h, g, m}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>}:
  Equal.cong(
    Maybe<&2, List<&2, String>>,
    Maybe<&2, Spec.Reply>,
    Answers.Reply.names,
    Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.nodes(R2, h, g, m), Lines.Store.versions(s, h)),
    Some{ns},
    Read.make(List<&2, String>, m, R2 => Groups.Groups.nodes(R2, h, g, m), Lines.Store.versions(s, h), R, ns, ev, lt, en)
  )

# the reply of the members of the group g of the store h at its version m,
# when the versions R of the store reach m: the members that R gives
def Members.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -R: List<&2, Types.Entry>,
  -ms: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
  em: {Groups.Groups.members(R, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {Answers.Answer.of(s, Spec.Question.Members{h, g, m}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>}:
  Equal.cong(
    Maybe<&2, List<&2, String>>,
    Maybe<&2, Spec.Reply>,
    Answers.Reply.names,
    Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.members(R2, h, g, m), Lines.Store.versions(s, h)),
    Some{ms},
    Read.make(List<&2, String>, m, R2 => Groups.Groups.members(R2, h, g, m), Lines.Store.versions(s, h), R, ms, ev, lt, em)
  )

# the reply of whether g is a group of the store h at its version m, when the
# versions R of the store reach m: what R gives
def IsGroup.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -R: List<&2, Types.Entry>,
  -y: Bool,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
  ey: {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>}
) -> {Answers.Answer.of(s, Spec.Question.IsGroup{h, g, m}) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>}:
  Equal.cong(
    Maybe<&2, Bool>,
    Maybe<&2, Spec.Reply>,
    Answers.Reply.yes,
    Answers.Store.read.of(Bool, m, R2 => Groups.Groups.is_group(R2, h, g, m), Lines.Store.versions(s, h)),
    Some{y},
    Read.make(Bool, m, R2 => Groups.Groups.is_group(R2, h, g, m), Lines.Store.versions(s, h), R, y, ev, lt, ey)
  )

# a reply of the nodes of a group of a store of the versions R is the nodes
# that R gives
def Nodes.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +R: List<&2, Types.Entry>,
  -ns: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  e: {Answers.Answer.of(s, Spec.Question.Nodes{h, g, m}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>}
) -> {Groups.Groups.nodes(R, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
    {Groups.Groups.nodes(R, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>},
    Read.at(
      List<&2, String>,
      m,
      R2 => Groups.Groups.nodes(R2, h, g, m),
      Lines.Store.versions(s, h),
      R,
      ns,
      ev,
      Reply.names_some(
        Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.nodes(R2, h, g, m), Lines.Store.versions(s, h)),
        ns
      )(e)
    )
  )

# a reply of the members of a group of a store of the versions R is the
# members that R gives
def Members.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +R: List<&2, Types.Entry>,
  -ms: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  e: {Answers.Answer.of(s, Spec.Question.Members{h, g, m}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>}
) -> {Groups.Groups.members(R, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
    {Groups.Groups.members(R, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>},
    Read.at(
      List<&2, String>,
      m,
      R2 => Groups.Groups.members(R2, h, g, m),
      Lines.Store.versions(s, h),
      R,
      ms,
      ev,
      Reply.names_some(
        Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.members(R2, h, g, m), Lines.Store.versions(s, h)),
        ms
      )(e)
    )
  )

# a reply of whether a name is a group of a store of the versions R is what R
# gives
def IsGroup.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +R: List<&2, Types.Entry>,
  -y: Bool,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  e: {Answers.Answer.of(s, Spec.Question.IsGroup{h, g, m}) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>}
) -> {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
    {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>},
    Read.at(
      Bool,
      m,
      R2 => Groups.Groups.is_group(R2, h, g, m),
      Lines.Store.versions(s, h),
      R,
      y,
      ev,
      Reply.yes_some(
        Answers.Store.read.of(Bool, m, R2 => Groups.Groups.is_group(R2, h, g, m), Lines.Store.versions(s, h)),
        y
      )(e)
    )
  )

# a store that replies with the members of a group at its version m has
# versions, and m is one of them
def Members.some(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -ms: List<&2, String>,
  e: {Answers.Answer.of(s, Spec.Question.Members{h, g, m}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>}
) -> Exists(
  List<&2, Types.Entry>,
  R => {
    Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
      }
        & {Groups.Groups.members(R, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}
    )
):
  Read.some(List<&2, String>, m, R2 => Groups.Groups.members(R2, h, g, m), Lines.Store.versions(s, h), ms)(
    Reply.names_some(
      Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.members(R2, h, g, m), Lines.Store.versions(s, h)),
      ms
    )(e)
  )

# a store that replies with the nodes of a group at its version m has
# versions, and m is one of them
def Nodes.some(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -ns: List<&2, String>,
  e: {Answers.Answer.of(s, Spec.Question.Nodes{h, g, m}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>}
) -> Exists(
  List<&2, Types.Entry>,
  R => {
    Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
      }
        & {Groups.Groups.nodes(R, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>}
    )
):
  Read.some(List<&2, String>, m, R2 => Groups.Groups.nodes(R2, h, g, m), Lines.Store.versions(s, h), ns)(
    Reply.names_some(
      Answers.Store.read.of(List<&2, String>, m, R2 => Groups.Groups.nodes(R2, h, g, m), Lines.Store.versions(s, h)),
      ns
    )(e)
  )

# a store that replies whether a name is a group at its version m has
# versions, and m is one of them
def IsGroup.some(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -y: Bool,
  e: {Answers.Answer.of(s, Spec.Question.IsGroup{h, g, m}) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>}
) -> Exists(
  List<&2, Types.Entry>,
  R => {
    Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
      }
        & {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>}
    )
):
  Read.some(Bool, m, R2 => Groups.Groups.is_group(R2, h, g, m), Lines.Store.versions(s, h), y)(
    Reply.yes_some(
      Answers.Store.read.of(Bool, m, R2 => Groups.Groups.is_group(R2, h, g, m), Lines.Store.versions(s, h)),
      y
    )(e)
  )

# a node that R gives to the group g is in the reply of the nodes of g
def Nodes.reply(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -R: List<&2, Types.Entry>,
  -x: String,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool},
  p: Exists(
    List<&2, String>,
    ns => {Groups.Groups.nodes(R, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>} & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
  )
) -> Exists(
  List<&2, String>,
  ns => {
    Answers.Answer.of(s, Spec.Question.Nodes{h, g, m}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  (ns, q) = p
  (en, c) = q
  (ns, (Nodes.make(s, h, g, m, R, ns, ev, lt, en), c))

# Core.group_nodes, for a member that is a group, with its premises as
# arguments
def Core.group_nodes.nested(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ms: List<&2, String>,
  +v: String,
  +R: List<&2, Types.Entry>,
  +x: String,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool},
  em: {Groups.Groups.members(R, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>},
  e2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  e4: {Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>},
  p: Exists(
    List<&2, String>,
    vs => {
      Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
  )
) -> Exists(
  List<&2, String>,
  ns => {
    Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  (+vs, q) = p
  (en, c) = q
  Nodes.reply(
    s,
    h,
    g,
    k,
    R,
    x,
    ev,
    lt,
    Groups.Groups.nodes_nested(
      R,
      h,
      g,
      k,
      ms,
      v,
      x,
      vs,
      em,
      e2,
      IsGroup.at(s, h, v, k, R, True{}, ev, e4),
      Nodes.at(s, h, v, k, R, vs, ev, en),
      c
    )
  )

# Core.group_nodes, with the versions of the store
def Core.group_nodes.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ms: List<&2, String>,
  +v: String,
  +R: List<&2, Types.Entry>,
  +e2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool},
  +em: {Groups.Groups.members(R, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> (
  {
    Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    )
  ):
  (
    e3 => Nodes.reply(
      s,
      h,
      g,
      k,
      R,
      v,
      ev,
      lt,
      Groups.Groups.nodes_member(R, h, g, k, ms, v, em, e2, IsGroup.at(s, h, v, k, R, False{}, ev, e3))
    ),
    e4 => +x => px => Core.group_nodes.nested(s, h, g, k, ms, v, R, x, ev, lt, em, e2, e4, px)
  )

# Core.group_nodes, once the store is known to have versions
def Core.group_nodes.open(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ms: List<&2, String>,
  +v: String,
  +e2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  p: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool
        }
          & {Groups.Groups.members(R, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>}
      )
  )
) -> (
  {
    Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    )
  ):
  (+R, q) = p
  (ev, q2) = q
  (lt, em) = q2
  Core.group_nodes.of(s, h, g, k, ms, v, R, e2, ev, lt, em)

# The nodes of a group are the members that are nodes, and the nodes of the
# members that are groups.
def Core.group_nodes(+s: Facts.Facts(), +h: Hashes.Hash, +g: String, +k: Nat, +ms: List<&2, String>, +v: String) -> {
  Answers.Answer.of(s, Spec.Question.Members{h, g, k}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
} -> {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} -> (
  {
    Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    )
  ):
  e1 => e2 => Core.group_nodes.open(s, h, g, k, ms, v, e2, Members.some(s, h, g, k, ms, e1))

# Core.group_nodes_only, for the member v: what R says of v, the replies say
def Core.group_nodes_only.case(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +k: Nat,
  -R: List<&2, Types.Entry>,
  +v: String,
  -x: String,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool},
  d: ({String.eq(v, x) == True{}: Bool} & {Groups.Groups.is_group(R, h, v, k) == Some{False{}}: Maybe<&2, Bool>}) | ({Groups.Groups.is_group(R, h, v, k) == Some{True{}}: Maybe<&2, Bool>} & Exists(List<&2, String>, vs => {Groups.Groups.nodes(R, h, v, k) == Some{vs}: Maybe<&2, List<&2, String>>} & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}))
) -> (
  {
    String.eq(v, x) == True{}: Bool
  }
    & {Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>}
)
  | (
    {
      Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    }
      & Exists(
        List<&2, String>,
        vs => {
          Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
        }
          & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
      )
  ):
  match d:
    case Inl{p}:
      (e, n) = p
      Inl{(e, IsGroup.make(s, h, v, k, R, False{}, ev, lt, n))}
    case Inr{q}:
      (y, r) = q
      Inr{(IsGroup.make(s, h, v, k, R, True{}, ev, lt, y), Nodes.reply(s, h, v, k, R, x, ev, lt, r))}

# Core.group_nodes_only, from what the versions R of the store say
def Core.group_nodes_only.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  -x: String,
  -R: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool},
  p: Exists(
    List<&2, String>,
    ms => {Groups.Groups.members(R, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>}
      & Exists(
        String,
        v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & (({String.eq(v, x) == True{}: Bool} & {Groups.Groups.is_group(R, h, v, k) == Some{False{}}: Maybe<&2, Bool>}) | ({Groups.Groups.is_group(R, h, v, k) == Some{True{}}: Maybe<&2, Bool>} & Exists(List<&2, String>, vs => {Groups.Groups.nodes(R, h, v, k) == Some{vs}: Maybe<&2, List<&2, String>>} & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool})))
      )
  )
) -> Exists(
  List<&2, String>,
  ms => {
    Answers.Answer.of(s, Spec.Question.Members{h, g, k}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
  }
    & Exists(
      String,
      v => {
        List.contains(~String, ~String.eq, ms, v) == True{}: Bool
      }
        & (
          (
            {
              String.eq(v, x) == True{}: Bool
            }
              & {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
                  }
                    & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                )
            )
        )
    )
):
  (ms, q) = p
  (em, q2) = q
  (+v, q3) = q2
  (c, d) = q3
  (ms, (Members.make(s, h, g, k, R, ms, ev, lt, em), (v, (c, Core.group_nodes_only.case(s, h, k, R, v, x, ev, lt, d)))))

# Core.group_nodes_only, once the store is known to have versions
def Core.group_nodes_only.open(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ns: List<&2, String>,
  +x: String,
  e2: {List.contains(~String, ~String.eq, ns, x) == True{}: Bool},
  p: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(k, List.length(&2, Types.Entry, R)) == True{}: Bool
        }
          & {Groups.Groups.nodes(R, h, g, k) == Some{ns}: Maybe<&2, List<&2, String>>}
      )
  )
) -> Exists(
  List<&2, String>,
  ms => {
    Answers.Answer.of(s, Spec.Question.Members{h, g, k}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
  }
    & Exists(
      String,
      v => {
        List.contains(~String, ~String.eq, ms, v) == True{}: Bool
      }
        & (
          (
            {
              String.eq(v, x) == True{}: Bool
            }
              & {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
                  }
                    & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                )
            )
        )
    )
):
  (+R, q) = p
  (ev, q2) = q
  (lt, en) = q2
  Core.group_nodes_only.of(s, h, g, k, x, R, ev, lt, Groups.Groups.nodes_only(R, h, g, k, ns, x, en, e2))

# And a group has no other nodes.
def Core.group_nodes_only(+s: Facts.Facts(), +h: Hashes.Hash, +g: String, +k: Nat, +ns: List<&2, String>, +x: String) -> {
  Answers.Answer.of(s, Spec.Question.Nodes{h, g, k}) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
} -> {List.contains(~String, ~String.eq, ns, x) == True{}: Bool} -> Exists(
  List<&2, String>,
  ms => {
    Answers.Answer.of(s, Spec.Question.Members{h, g, k}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
  }
    & Exists(
      String,
      v => {
        List.contains(~String, ~String.eq, ms, v) == True{}: Bool
      }
        & (
          (
            {
              String.eq(v, x) == True{}: Bool
            }
              & {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(s, Spec.Question.IsGroup{h, v, k}) == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(s, Spec.Question.Nodes{h, v, k}) == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
                  }
                    & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                )
            )
        )
    )
):
  e1 => e2 => Core.group_nodes_only.open(s, h, g, k, ns, x, e2, Nodes.some(s, h, g, k, ns, e1))

# Versions and what made them
# ---------------------------

# the two readings of the request of an entry agree
def Entry.request_same(e: Types.Entry) -> {Answers.Entry.request(e) == Groups.Entry.request(e): Spec.Request}:
  match e:
    case Types.Entry{Types.Pick{Types.Ask{i, q, r}, pins}, k}:
      {==}

# a reply of the id i comes from an entry of the id i
def Reply.id_some(m: Maybe<&2, Types.Entry>, -i: Ledgers.Id) -> {
  Answers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> Exists(Types.Entry, e => {m == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Types.Entry, e => {None{} == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h)
      )
    case Some{+x}:
      h => (
        x,
        (
          {==},
          Shared.Maybe.some_inj(
            Ledgers.Id,
            Lines.Entry.id(x),
            i,
            Equal.cong(
              Maybe<&2, Spec.Reply>,
              Maybe<&2, Ledgers.Id>,
              Reply.id_of,
              Some{Spec.Reply.Id{Lines.Entry.id(x)}},
              Some{Spec.Reply.Id{i}},
              h
            )
          )
        )
      )

# the reply of the id of version j of a store: the id of entry j of its
# versions
def Version.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  -R: List<&2, Types.Entry>,
  +j: Nat,
  -e: Types.Entry,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  eg: {List.get(&2, Types.Entry, R, j) == Some{e}: Maybe<&2, Types.Entry>}
) -> {
  Answers.Answer.of(s, Spec.Question.Version{Ledgers.Line{h, None{}}, j}) == Some{Spec.Reply.Id{Lines.Entry.id(e)}}: Maybe<&2, Spec.Reply>
}:
  %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Store.versions(s, h), Some{R}, ev): {Answers.Reply.id(Lines.Line.at.of(_, j)) == Some{Spec.Reply.Id{Lines.Entry.id(e)}}: Maybe<&2, Spec.Reply>}
  %Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, R, j), Some{e}, eg): {Answers.Reply.id(_) == Some{Spec.Reply.Id{Lines.Entry.id(e)}}: Maybe<&2, Spec.Reply>}
  {==}

# the reply of the request of the id of entry j of the versions of a store:
# the request of that entry
def Request.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  -R: List<&2, Types.Entry>,
  +j: Nat,
  -e: Types.Entry,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  eg: {List.get(&2, Types.Entry, R, j) == Some{e}: Maybe<&2, Types.Entry>},
  ei: {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, R, Lines.Entry.id(e)) == Some{j}: Maybe<&2, Nat>}
) -> {
  Answers.Answer.of(s, Spec.Question.Request{Ledgers.Line{h, None{}}, Lines.Entry.id(e)}) == Some{Spec.Reply.Ask{Answers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
}:
  %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Store.versions(s, h), Some{R}, ev): {Answers.Reply.ask(Answers.Line.find.of(Lines.Entry.id(e), _)) == Some{Spec.Reply.Ask{Answers.Entry.request(e)}}: Maybe<&2, Spec.Reply>}
  %Equal.sym(Maybe<&2, Nat>, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, R, Lines.Entry.id(e)), Some{j}, ei): {Answers.Reply.ask(Answers.Versions.find.at(R, _)) == Some{Spec.Reply.Ask{Answers.Entry.request(e)}}: Maybe<&2, Spec.Reply>}
  %Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, R, j), Some{e}, eg): {Answers.Reply.ask(Maybe.map(&2, Types.Entry, Answers.Found, e2 => Answers.Found{j, e2}, _)) == Some{Spec.Reply.Ask{Answers.Entry.request(e)}}: Maybe<&2, Spec.Reply>}
  {==}

# Made.of_at, for the entry e of the version
def Made.of_at.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -r: Spec.Request,
  +e: Types.Entry,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +eg: {List.get(&2, Types.Entry, R, j) == Some{e}: Maybe<&2, Types.Entry>},
  er: {Groups.Entry.request(e) == r: Spec.Request}
) -> Mirror.Made(s, Ledgers.Line{h, None{}}, j, Lines.Entry.id(e), r):
  (
    Version.make(s, h, R, j, e, ev, eg),
    Own.cast(
      Spec.Request,
      w => {
        Answers.Answer.of(s, Spec.Question.Request{Ledgers.Line{h, None{}}, Lines.Entry.id(e)}) == Some{Spec.Reply.Ask{w}}: Maybe<&2, Spec.Reply>
      },
      Answers.Entry.request(e),
      r,
      Equal.trans(Spec.Request, Answers.Entry.request(e), Groups.Entry.request(e), r, Entry.request_same(e), er),
      Request.make(
        s,
        h,
        R,
        j,
        e,
        ev,
        eg,
        Versions.Line.versions_index(s, Ledgers.Line{h, None{}}, R, j, e)(ev)(eg)
      )
    )
  )

# a version of the versions R of a store, made by the request r, is the
# decision of a request that asked for r
def Made.of_at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -r: Spec.Request,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  a: Groups.Groups.At(R, j, r)
) -> Exists(Ledgers.Id, i => Mirror.Made(s, Ledgers.Line{h, None{}}, j, i, r)):
  (+e, p) = a
  (eg, er) = p
  (Lines.Entry.id(e), Made.of_at.of(s, h, R, j, r, e, ev, eg, er))

# At.of_made, for the entry e of the version
def At.of_made.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +e: Types.Entry,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +eg: {List.get(&2, Types.Entry, R, j) == Some{e}: Maybe<&2, Types.Entry>},
  ei: {Lines.Entry.id(e) == i: Ledgers.Id},
  e2: {Answers.Answer.of(s, Spec.Question.Request{Ledgers.Line{h, None{}}, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>}
) -> {Groups.Entry.request(e) == r: Spec.Request}:
  Equal.trans(
    Spec.Request,
    Groups.Entry.request(e),
    Answers.Entry.request(e),
    r,
    Equal.sym(Spec.Request, Answers.Entry.request(e), Groups.Entry.request(e), Entry.request_same(e)),
    Shared.Maybe.some_inj(
      Spec.Request,
      Answers.Entry.request(e),
      r,
      Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, Spec.Request>,
        Reply.ask_of,
        Some{Spec.Reply.Ask{Answers.Entry.request(e)}},
        Some{Spec.Reply.Ask{r}},
        Own.cast(
          Maybe<&2, Types.Entry>,
          w => {
            Answers.Reply.ask(Maybe.map(&2, Types.Entry, Answers.Found, e3 => Answers.Found{j, e3}, w)) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
          },
          List.get(&2, Types.Entry, R, j),
          Some{e},
          eg,
          Own.cast(
            Maybe<&2, Nat>,
            w => {Answers.Reply.ask(Answers.Versions.find.at(R, w)) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>},
            Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, R, Lines.Entry.id(e)),
            Some{j},
            Versions.Line.versions_index(s, Ledgers.Line{h, None{}}, R, j, e)(ev)(eg),
            Own.cast(
              Maybe<&2, List<&2, Types.Entry>>,
              w => {
                Answers.Reply.ask(Answers.Line.find.of(Lines.Entry.id(e), w)) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
              },
              Lines.Store.versions(s, h),
              Some{R},
              ev,
              Own.cast(
                Ledgers.Id,
                w => {
                  Answers.Reply.ask(Answers.Line.find.of(w, Lines.Store.versions(s, h))) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
                },
                i,
                Lines.Entry.id(e),
                Equal.sym(Ledgers.Id, Lines.Entry.id(e), i, ei),
                e2
              )
            )
          )
        )
      )
    )
  )

# At.of_made, once the entry of the version is known
def At.of_made.open(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(Types.Entry, e => {List.get(&2, Types.Entry, R, j) == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}),
  e2: {Answers.Answer.of(s, Spec.Question.Request{Ledgers.Line{h, None{}}, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>}
) -> Groups.Groups.At(R, j, r):
  (+e, q) = p
  (+eg, ei) = q
  (e, (eg, At.of_made.of(s, h, R, j, i, r, e, ev, eg, ei, e2)))

# a version of a store that is the decision of a request that asked for r is
# a version of its versions R made by r
def At.of_made(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  mk: Mirror.Made(s, Ledgers.Line{h, None{}}, j, i, r)
) -> Groups.Groups.At(R, j, r):
  (e1, e2) = mk
  At.of_made.open(
    s,
    h,
    R,
    j,
    i,
    r,
    ev,
    Reply.id_some(List.get(&2, Types.Entry, R, j), i)(
      Own.cast(
        Maybe<&2, List<&2, Types.Entry>>,
        w => {Answers.Reply.id(Lines.Line.at.of(w, j)) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>},
        Lines.Store.versions(s, h),
        Some{R},
        ev,
        e1
      )
    ),
    e2
  )

# the latest version of the store h up to m that decides r is a version of
# its versions R made by r, at most m
def At.of_latest(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -m: Nat,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  l: Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, r)
) -> Groups.Groups.At(R, j, r) & {Nat.is_le(j, m) == True{}: Bool}:
  (ex, le) = l
  (i, mk) = ex
  (At.of_made(s, h, R, j, i, r, ev, mk), le)

# a version of the versions R of the store h made by r, at most m, is one
# that decides r up to m
def Latest.of_at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  -m: Nat,
  -r: Spec.Request,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  p: Groups.Groups.At(R, j, r) & {Nat.is_le(j, m) == True{}: Bool}
) -> Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, r):
  (a, le) = p
  (Made.of_at(s, h, R, j, r, ev, a), le)

# The members of a group
# ----------------------

# Core.members_decided, from the latest Group among the versions R of the
# store
def Core.members_decided.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -ms: List<&2, String>,
  +R: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(
    Nat,
    j => (Groups.Groups.At(R, j, Spec.Request.Group{h, g, ms}) & {Nat.is_le(j, m) == True{}: Bool})
      & (@j2: Nat -> @ms2: List<&2, String> -> Groups.Groups.At(R, j2, Spec.Request.Group{h, g, ms2}) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool})
  )
) -> Exists(
  Nat,
  j => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    & (
      @j2: Nat -> @ms2: List<&2, String> -> Mirror.Latest(
        s,
        Ledgers.Line{h, None{}},
        j2,
        m,
        Spec.Request.Group{h, g, ms2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+j, q) = p
  (hit, later) = q
  (
    j,
    (
      Latest.of_at(s, h, R, j, m, Spec.Request.Group{h, g, ms}, ev, hit),
      +j2 => +ms2 => l => Groups.Pair.use(
        Groups.Groups.At(R, j2, Spec.Request.Group{h, g, ms2}),
        {Nat.is_le(j2, m) == True{}: Bool},
        {Nat.is_le(j2, j) == True{}: Bool},
        At.of_latest(s, h, R, j2, m, Spec.Request.Group{h, g, ms2}, ev, l),
        a => le => later(j2)(ms2)(a)(le)
      )
    )
  )

# Core.members_decided, once the store is known to have versions
def Core.members_decided.open(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ms: List<&2, String>,
  p: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
        }
          & {Groups.Groups.members(R, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}
      )
  )
) -> Exists(
  Nat,
  j => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    & (
      @j2: Nat -> @ms2: List<&2, String> -> Mirror.Latest(
        s,
        Ledgers.Line{h, None{}},
        j2,
        m,
        Spec.Request.Group{h, g, ms2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+R, q) = p
  (ev, q2) = q
  (lt, em) = q2
  Core.members_decided.of(s, h, g, m, ms, R, ev, Groups.Groups.members_latest(R, h, g, m, ms, em))

# The members of a group are those that the latest Group of its name, up to that
# version of the store, names.
def Core.members_decided(+s: Facts.Facts(), +h: Hashes.Hash, +g: String, +m: Nat, +ms: List<&2, String>) -> {
  Answers.Answer.of(s, Spec.Question.Members{h, g, m}) == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  j => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    & (
      @j2: Nat -> @ms2: List<&2, String> -> Mirror.Latest(
        s,
        Ledgers.Line{h, None{}},
        j2,
        m,
        Spec.Request.Group{h, g, ms2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  e => Core.members_decided.open(s, h, g, m, ms, Members.some(s, h, g, m, ms, e))

# Core.groups_decided, for a name that is a group, from a Group among the
# versions R of the store
def Core.groups_decided.yes(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +R: List<&2, Types.Entry>,
  ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(Nat, j => Exists(List<&2, String>, ms => Groups.Groups.At(R, j, Spec.Request.Group{h, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}))
) -> Exists(
  Nat,
  j => Exists(
    List<&2, String>,
    ms => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
  )
):
  (+j, q) = p
  (ms, hit) = q
  (j, (ms, Latest.of_at(s, h, R, j, m, Spec.Request.Group{h, g, ms}, ev, hit)))

# Core.groups_decided, with the versions R of the store
def Core.groups_decided.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +y: Bool,
  +R: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>},
  +ey: {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>}
) -> (
  {
    y == True{}: Bool
  } -> Exists(
    Nat,
    j => Exists(
      List<&2, String>,
      ms => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    )
  )
)
  & (
    {
      y == False{}: Bool
    } -> @j: Nat -> @ms: List<&2, String> -> Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms}) -> Empty
  ):
  (
    ty => Core.groups_decided.yes(
      s,
      h,
      g,
      m,
      R,
      ev,
      Groups.Groups.is_group_yes(
        R,
        h,
        g,
        m,
        Own.cast(Bool, w => {Groups.Groups.is_group(R, h, g, m) == Some{w}: Maybe<&2, Bool>}, y, True{}, ty, ey)
      )
    ),
    fy => +j => +ms => l => Groups.Pair.use(
      Groups.Groups.At(R, j, Spec.Request.Group{h, g, ms}),
      {Nat.is_le(j, m) == True{}: Bool},
      Empty,
      At.of_latest(s, h, R, j, m, Spec.Request.Group{h, g, ms}, ev, l),
      a => le => Groups.Groups.is_group_no(
        R,
        h,
        g,
        m,
        Own.cast(Bool, w => {Groups.Groups.is_group(R, h, g, m) == Some{w}: Maybe<&2, Bool>}, y, False{}, fy, ey)
      )(j)(ms)(a)(le)
    )
  )

# Core.groups_decided, once the store is known to have versions
def Core.groups_decided.open(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +y: Bool,
  p: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
        }
          & {Groups.Groups.is_group(R, h, g, m) == Some{y}: Maybe<&2, Bool>}
      )
  )
) -> (
  {
    y == True{}: Bool
  } -> Exists(
    Nat,
    j => Exists(
      List<&2, String>,
      ms => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    )
  )
)
  & (
    {
      y == False{}: Bool
    } -> @j: Nat -> @ms: List<&2, String> -> Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms}) -> Empty
  ):
  (+R, q) = p
  (ev, q2) = q
  (lt, ey) = q2
  Core.groups_decided.of(s, h, g, m, y, R, ev, ey)

# A name is a group at a version of the store exactly when a Group of that name
# was decided up to it.
def Core.groups_decided(+s: Facts.Facts(), +h: Hashes.Hash, +g: String, +m: Nat, +y: Bool) -> {
  Answers.Answer.of(s, Spec.Question.IsGroup{h, g, m}) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
} -> (
  {
    y == True{}: Bool
  } -> Exists(
    Nat,
    j => Exists(
      List<&2, String>,
      ms => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
    )
  )
)
  & (
    {
      y == False{}: Bool
    } -> @j: Nat -> @ms: List<&2, String> -> Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms}) -> Empty
  ):
  e => Core.groups_decided.open(s, h, g, m, y, IsGroup.some(s, h, g, m, y, e))
