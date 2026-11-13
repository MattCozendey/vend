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
