import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./answers.bend as Answers
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./mirror.bend as Mirror
import ./run/answers.bend as RAnswers
import ./run/lines.bend as RLines
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
def Reply.names_some(
  m: Maybe<&2, List<&2, String>>,
  -ns: List<&2, String>
) -> {
  RAnswers.Reply.names(m) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
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
def Reply.yes_some(
  m: Maybe<&2, Bool>,
  -y: Bool
) -> {
  RAnswers.Reply.yes(m) == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
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
def Reply.number_some(
  m: Maybe<&2, Nat>,
  -k: Nat
) -> {
  RAnswers.Reply.number(m) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
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
def When.some(
  -A: Data,
  b: Bool,
  -y: Maybe<&2, A>,
  -x: A,
  h: {Shared.Maybe.when(A, b, u => y) == Some{x}: Maybe<&2, A>}
) -> {b == True{}: Bool}
  & {y == Some{x}: Maybe<&2, A>}:
  match b:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd(
        {False{} == True{}: Bool} & {y == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, h)
      )

# a read of a store that answers: the store has versions, and the version read
# is one of them
def Read.some(
  -A: Data,
  +m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>,
  v: Maybe<&2, List<&2, Types.Entry>>,
  -x: A
) -> {
  RAnswers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>
} -> Exists(
  List<&2, Types.Entry>,
  R => {
    v == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
      }
        & {f(R) == Some{x}: Maybe<&2, A>}
    )
):
  match v:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          R => {
            None{} == Some{R}: Maybe<&2, List<&2, Types.Entry>>
          }
            & (
              {
                Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
              }
                & {f(R) == Some{x}: Maybe<&2, A>}
            )
        ),
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Some{+R}:
      h => (R, ({==}, When.some(A, Nat.is_lt(m, List.length(&2, Types.Entry, R)), f(R), x, h)))

# a read of a store of the versions r that answers: the version read is one of
# r, and the answer is the read of r
def Read.at(
  -A: Data,
  +m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>,
  -v: Maybe<&2, List<&2, Types.Entry>>,
  +r: List<&2, Types.Entry>,
  -x: A,
  ev: {v == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  e: {RAnswers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>}
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool
}
  & {f(r) == Some{x}: Maybe<&2, A>}:
  When.some(
    A,
    Nat.is_lt(m, List.length(&2, Types.Entry, r)),
    f(r),
    x,
    Own.cast(
      Maybe<&2, List<&2, Types.Entry>>,
      w => {RAnswers.Store.read.of(A, m, f, w) == Some{x}: Maybe<&2, A>},
      v,
      Some{r},
      ev,
      e
    )
  )

# a read of a store of the versions r answers the read of r, when the version
# read is one of r
def Read.make(
  -A: Data,
  -m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>,
  -v: Maybe<&2, List<&2, Types.Entry>>,
  -r: List<&2, Types.Entry>,
  -x: A,
  ev: {v == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
  ef: {f(r) == Some{x}: Maybe<&2, A>}
) -> {RAnswers.Store.read.of(A, m, f, v) == Some{x}: Maybe<&2, A>}:
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    v,
    Some{r},
    ev
  ): {RAnswers.Store.read.of(A, m, f, _) == Some{x}: Maybe<&2, A>}
  %Equal.sym(
    Bool,
    Nat.is_lt(m, List.length(&2, Types.Entry, r)),
    True{},
    lt
  ): {Shared.Maybe.when(A, _, u => f(r)) == Some{x}: Maybe<&2, A>}
  ef

# The nodes of a group
# --------------------

# the reply of the nodes of the group g of the store h at its version m, when
# the versions r of the store reach m: the nodes that r gives
def Nodes.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -r: List<&2, Types.Entry>,
  -ns: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
  en: {Groups.Groups.nodes(r, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>}
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Nodes{h, g, m}
  )
    == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
}:
  Equal.cong(
    Maybe<&2, List<&2, String>>,
    Maybe<&2, Spec.Reply>,
    RAnswers.Reply.names,
    RAnswers.Store.read.of(
      List<&2, String>,
      m,
      R2 => Groups.Groups.nodes(R2, h, g, m),
      Lines.Store.versions(s, h)
    ),
    Some{ns},
    Read.make(
      List<&2, String>,
      m,
      R2 => Groups.Groups.nodes(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      ns,
      ev,
      lt,
      en
    )
  )

# the reply of the members of the group g of the store h at its version m,
# when the versions r of the store reach m: the members that r gives
def Members.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -r: List<&2, Types.Entry>,
  -ms: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
  em: {Groups.Groups.members(r, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Members{h, g, m}
  )
    == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
}:
  Equal.cong(
    Maybe<&2, List<&2, String>>,
    Maybe<&2, Spec.Reply>,
    RAnswers.Reply.names,
    RAnswers.Store.read.of(
      List<&2, String>,
      m,
      R2 => Groups.Groups.members(R2, h, g, m),
      Lines.Store.versions(s, h)
    ),
    Some{ms},
    Read.make(
      List<&2, String>,
      m,
      R2 => Groups.Groups.members(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      ms,
      ev,
      lt,
      em
    )
  )

# the reply of whether g is a group of the store h at its version m, when the
# versions r of the store reach m: what r gives
def IsGroup.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -r: List<&2, Types.Entry>,
  -y: Bool,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
  ey: {Groups.Groups.is_group(r, h, g, m) == Some{y}: Maybe<&2, Bool>}
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.IsGroup{h, g, m}
  )
    == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
}:
  Equal.cong(
    Maybe<&2, Bool>,
    Maybe<&2, Spec.Reply>,
    RAnswers.Reply.yes,
    RAnswers.Store.read.of(
      Bool,
      m,
      R2 => Groups.Groups.is_group(R2, h, g, m),
      Lines.Store.versions(s, h)
    ),
    Some{y},
    Read.make(
      Bool,
      m,
      R2 => Groups.Groups.is_group(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      y,
      ev,
      lt,
      ey
    )
  )

# a reply of the nodes of a group of a store of the versions r is the nodes
# that r gives
def Nodes.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +r: List<&2, Types.Entry>,
  -ns: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.Nodes{h, g, m}
    )
      == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
  }
) -> {Groups.Groups.nodes(r, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
    {Groups.Groups.nodes(r, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>},
    Read.at(
      List<&2, String>,
      m,
      R2 => Groups.Groups.nodes(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      ns,
      ev,
      Reply.names_some(
        RAnswers.Store.read.of(
          List<&2, String>,
          m,
          R2 => Groups.Groups.nodes(R2, h, g, m),
          Lines.Store.versions(s, h)
        ),
        ns
      )(e)
    )
  )

# a reply of the members of a group of a store of the versions r is the
# members that r gives
def Members.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +r: List<&2, Types.Entry>,
  -ms: List<&2, String>,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.Members{h, g, m}
    )
      == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
  }
) -> {Groups.Groups.members(r, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
    {Groups.Groups.members(r, h, g, m) == Some{ms}: Maybe<&2, List<&2, String>>},
    Read.at(
      List<&2, String>,
      m,
      R2 => Groups.Groups.members(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      ms,
      ev,
      Reply.names_some(
        RAnswers.Store.read.of(
          List<&2, String>,
          m,
          R2 => Groups.Groups.members(R2, h, g, m),
          Lines.Store.versions(s, h)
        ),
        ms
      )(e)
    )
  )

# a reply of whether a name is a group of a store of the versions r is what r
# gives
def IsGroup.at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +r: List<&2, Types.Entry>,
  -y: Bool,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, g, m}
    )
      == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
  }
) -> {Groups.Groups.is_group(r, h, g, m) == Some{y}: Maybe<&2, Bool>}:
  Pair.snd(
    {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
    {Groups.Groups.is_group(r, h, g, m) == Some{y}: Maybe<&2, Bool>},
    Read.at(
      Bool,
      m,
      R2 => Groups.Groups.is_group(R2, h, g, m),
      Lines.Store.versions(s, h),
      r,
      y,
      ev,
      Reply.yes_some(
        RAnswers.Store.read.of(
          Bool,
          m,
          R2 => Groups.Groups.is_group(R2, h, g, m),
          Lines.Store.versions(s, h)
        ),
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
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.Members{h, g, m}
    )
      == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
  }
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
  Read.some(
    List<&2, String>,
    m,
    R2 => Groups.Groups.members(R2, h, g, m),
    Lines.Store.versions(s, h),
    ms
  )(
    Reply.names_some(
      RAnswers.Store.read.of(
        List<&2, String>,
        m,
        R2 => Groups.Groups.members(R2, h, g, m),
        Lines.Store.versions(s, h)
      ),
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
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.Nodes{h, g, m}
    )
      == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
  }
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
  Read.some(
    List<&2, String>,
    m,
    R2 => Groups.Groups.nodes(R2, h, g, m),
    Lines.Store.versions(s, h),
    ns
  )(
    Reply.names_some(
      RAnswers.Store.read.of(
        List<&2, String>,
        m,
        R2 => Groups.Groups.nodes(R2, h, g, m),
        Lines.Store.versions(s, h)
      ),
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
  e: {
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, g, m}
    )
      == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
  }
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
  Read.some(
    Bool,
    m,
    R2 => Groups.Groups.is_group(R2, h, g, m),
    Lines.Store.versions(s, h),
    y
  )(
    Reply.yes_some(
      RAnswers.Store.read.of(
        Bool,
        m,
        R2 => Groups.Groups.is_group(R2, h, g, m),
        Lines.Store.versions(s, h)
      ),
      y
    )(e)
  )

# a node that r gives to the group g is in the reply of the nodes of g
def Nodes.reply(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -r: List<&2, Types.Entry>,
  -x: String,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool},
  p: Exists(
    List<&2, String>,
    ns => {
      Groups.Groups.nodes(r, h, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
    }
      & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
  )
) -> Exists(
  List<&2, String>,
  ns => {
    Answers.Answer.of(
      s,
      Spec.Question.Nodes{h, g, m}
    )
      == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  (ns, q) = p
  (en, c) = q
  (ns, (Nodes.make(s, h, g, m, r, ns, ev, lt, en), c))

# Core.group_nodes, for a member that is a group, with its premises as
# arguments
def Core.group_nodes.nested(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ms: List<&2, String>,
  +v: String,
  +r: List<&2, Types.Entry>,
  +x: String,
  +ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  lt: {Nat.is_lt(k, List.length(&2, Types.Entry, r)) == True{}: Bool},
  em: {Groups.Groups.members(r, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>},
  e2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  e4: {
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, v, k}
    )
      == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
  },
  p: Exists(
    List<&2, String>,
    vs => {
      Answers.Answer.of(
        s,
        Spec.Question.Nodes{h, v, k}
      )
        == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
  )
) -> Exists(
  List<&2, String>,
  ns => {
    Answers.Answer.of(
      s,
      Spec.Question.Nodes{h, g, k}
    )
      == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
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
    r,
    x,
    ev,
    lt,
    Groups.Groups.nodes_nested(
      r,
      h,
      g,
      k,
      ms,
      v,
      x,
      vs,
      em,
      e2,
      IsGroup.at(s, h, v, k, r, True{}, ev, e4),
      Nodes.at(s, h, v, k, r, vs, ev, en),
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
  +r: List<&2, Types.Entry>,
  +e2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  +ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, r)) == True{}: Bool},
  +em: {Groups.Groups.members(r, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> (
  {
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, v, k}
    )
      == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(
        s,
        Spec.Question.Nodes{h, g, k}
      )
        == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(
        s,
        Spec.Question.IsGroup{h, v, k}
      )
        == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, v, k}
        )
          == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, g, k}
        )
          == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
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
      r,
      v,
      ev,
      lt,
      Groups.Groups.nodes_member(
        r,
        h,
        g,
        k,
        ms,
        v,
        em,
        e2,
        IsGroup.at(s, h, v, k, r, False{}, ev, e3)
      )
    ),
    e4 => +x => px => Core.group_nodes.nested(s, h, g, k, ms, v, r, x, ev, lt, em, e2, e4, px)
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
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, v, k}
    )
      == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(
        s,
        Spec.Question.Nodes{h, g, k}
      )
        == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(
        s,
        Spec.Question.IsGroup{h, v, k}
      )
        == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, v, k}
        )
          == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, g, k}
        )
          == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
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
def Core.group_nodes(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ms: List<&2, String>,
  +v: String
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Members{h, g, k}
  )
    == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
} -> {
  List.contains(~String, ~String.eq, ms, v) == True{}: Bool
} -> (
  {
    Answers.Answer.of(
      s,
      Spec.Question.IsGroup{h, v, k}
    )
      == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
  } -> Exists(
    List<&2, String>,
    ns => {
      Answers.Answer.of(
        s,
        Spec.Question.Nodes{h, g, k}
      )
        == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
    }
      & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
  )
)
  & (
    {
      Answers.Answer.of(
        s,
        Spec.Question.IsGroup{h, v, k}
      )
        == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    } -> @x: String -> Exists(
      List<&2, String>,
      vs => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, v, k}
        )
          == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
    ) -> Exists(
      List<&2, String>,
      ns => {
        Answers.Answer.of(
          s,
          Spec.Question.Nodes{h, g, k}
        )
          == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    )
  ):
  e1 => e2 => Core.group_nodes.open(s, h, g, k, ms, v, e2, Members.some(s, h, g, k, ms, e1))

# Core.group_nodes_only, for the member v: what store says of v, the replies say
def Core.group_nodes_only.case(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +k: Nat,
  -store: List<&2, Types.Entry>,
  +v: String,
  -x: String,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, store)) == True{}: Bool},
  d: (
    {
      String.eq(v, x) == True{}: Bool
    }
      & {Groups.Groups.is_group(store, h, v, k) == Some{False{}}: Maybe<&2, Bool>}
  )
    | (
      {
        Groups.Groups.is_group(store, h, v, k) == Some{True{}}: Maybe<&2, Bool>
      }
        & Exists(
          List<&2, String>,
          vs => {
            Groups.Groups.nodes(store, h, v, k) == Some{vs}: Maybe<&2, List<&2, String>>
          }
            & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
        )
    )
) -> (
  {
    String.eq(v, x) == True{}: Bool
  }
    & {
      Answers.Answer.of(
        s,
        Spec.Question.IsGroup{h, v, k}
      )
        == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
    }
)
  | (
    {
      Answers.Answer.of(
        s,
        Spec.Question.IsGroup{h, v, k}
      )
        == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
    }
      & Exists(
        List<&2, String>,
        vs => {
          Answers.Answer.of(
            s,
            Spec.Question.Nodes{h, v, k}
          )
            == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
        }
          & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
      )
  ):
  match d:
    case Inl{p}:
      (e, n) = p
      Inl{(e, IsGroup.make(s, h, v, k, store, False{}, ev, lt, n))}
    case Inr{q}:
      (y, r) = q
      Inr{
        (
          IsGroup.make(s, h, v, k, store, True{}, ev, lt, y),
          Nodes.reply(s, h, v, k, store, x, ev, lt, r)
        )
      }

# Core.group_nodes_only, from what the versions r of the store say
def Core.group_nodes_only.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  -x: String,
  -r: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  +lt: {Nat.is_lt(k, List.length(&2, Types.Entry, r)) == True{}: Bool},
  p: Exists(
    List<&2, String>,
    ms => {
      Groups.Groups.members(r, h, g, k) == Some{ms}: Maybe<&2, List<&2, String>>
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
                & {Groups.Groups.is_group(r, h, v, k) == Some{False{}}: Maybe<&2, Bool>}
            )
              | (
                {
                  Groups.Groups.is_group(r, h, v, k) == Some{True{}}: Maybe<&2, Bool>
                }
                  & Exists(
                    List<&2, String>,
                    vs => {
                      Groups.Groups.nodes(r, h, v, k) == Some{vs}: Maybe<&2, List<&2, String>>
                    }
                      & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                  )
              )
          )
      )
  )
) -> Exists(
  List<&2, String>,
  ms => {
    Answers.Answer.of(
      s,
      Spec.Question.Members{h, g, k}
    )
      == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
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
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(
                      s,
                      Spec.Question.Nodes{h, v, k}
                    )
                      == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
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
  (
    ms,
    (
      Members.make(s, h, g, k, r, ms, ev, lt, em),
      (v, (c, Core.group_nodes_only.case(s, h, k, r, v, x, ev, lt, d)))
    )
  )

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
    Answers.Answer.of(
      s,
      Spec.Question.Members{h, g, k}
    )
      == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
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
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(
                      s,
                      Spec.Question.Nodes{h, v, k}
                    )
                      == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
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
  Core.group_nodes_only.of(
    s,
    h,
    g,
    k,
    x,
    R,
    ev,
    lt,
    Groups.Groups.nodes_only(R, h, g, k, ns, x, en, e2)
  )

# And a group has no other nodes.
def Core.group_nodes_only(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +k: Nat,
  +ns: List<&2, String>,
  +x: String
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Nodes{h, g, k}
  )
    == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
} -> {
  List.contains(~String, ~String.eq, ns, x) == True{}: Bool
} -> Exists(
  List<&2, String>,
  ms => {
    Answers.Answer.of(
      s,
      Spec.Question.Members{h, g, k}
    )
      == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
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
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{False{}}}: Maybe<&2, Spec.Reply>
              }
          )
            | (
              {
                Answers.Answer.of(
                  s,
                  Spec.Question.IsGroup{h, v, k}
                )
                  == Some{Spec.Reply.Yes{True{}}}: Maybe<&2, Spec.Reply>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Answers.Answer.of(
                      s,
                      Spec.Question.Nodes{h, v, k}
                    )
                      == Some{Spec.Reply.Names{vs}}: Maybe<&2, Spec.Reply>
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
def Entry.request_same(
  e: Types.Entry
) -> {RAnswers.Entry.request(e) == Groups.Entry.request(e): Spec.Request}:
  match e:
    case Types.Entry{Types.Pick{Types.Ask{i, q, r}, pins}, k}:
      {==}

# a reply of the id i comes from an entry of the id i
def Reply.id_some(
  m: Maybe<&2, Types.Entry>,
  -i: Ledgers.Id
) -> {
  RAnswers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Types.Entry,
  e => {m == Some{e}: Maybe<&2, Types.Entry>} & {RLines.Entry.id(e) == i: Ledgers.Id}
):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(
          Types.Entry,
          e => {None{} == Some{e}: Maybe<&2, Types.Entry>} & {RLines.Entry.id(e) == i: Ledgers.Id}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h)
      )
    case Some{+x}:
      h => (
        x,
        (
          {==},
          Shared.Maybe.some_inj(
            Ledgers.Id,
            RLines.Entry.id(x),
            i,
            Equal.cong(
              Maybe<&2, Spec.Reply>,
              Maybe<&2, Ledgers.Id>,
              Reply.id_of,
              Some{Spec.Reply.Id{RLines.Entry.id(x)}},
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
  -r: List<&2, Types.Entry>,
  +j: Nat,
  -e: Types.Entry,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  eg: {List.get(&2, Types.Entry, r, j) == Some{e}: Maybe<&2, Types.Entry>}
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Version{Ledgers.Line{h, None{}}, j}
  )
    == Some{Spec.Reply.Id{RLines.Entry.id(e)}}: Maybe<&2, Spec.Reply>
}:
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    Lines.Store.versions(s, h),
    Some{r},
    ev
  ): {
    RAnswers.Reply.id(
      RLines.Line.at.of(_, j)
    )
      == Some{Spec.Reply.Id{RLines.Entry.id(e)}}: Maybe<&2, Spec.Reply>
  }
  %Equal.sym(
    Maybe<&2, Types.Entry>,
    List.get(&2, Types.Entry, r, j),
    Some{e},
    eg
  ): {RAnswers.Reply.id(_) == Some{Spec.Reply.Id{RLines.Entry.id(e)}}: Maybe<&2, Spec.Reply>}
  {==}

# the reply of the request of the id of entry j of the versions of a store:
# the request of that entry
def Request.make(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  -r: List<&2, Types.Entry>,
  +j: Nat,
  -e: Types.Entry,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  eg: {List.get(&2, Types.Entry, r, j) == Some{e}: Maybe<&2, Types.Entry>},
  ei: {
    Lists.List.index(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      r,
      RLines.Entry.id(e)
    )
      == Some{j}: Maybe<&2, Nat>
  }
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Request{Ledgers.Line{h, None{}}, RLines.Entry.id(e)}
  )
    == Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
}:
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    Lines.Store.versions(s, h),
    Some{r},
    ev
  ): {
    RAnswers.Reply.ask(
      RAnswers.Line.find.of(RLines.Entry.id(e), _)
    )
      == Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
  }
  %Equal.sym(
    Maybe<&2, Nat>,
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, r, RLines.Entry.id(e)),
    Some{j},
    ei
  ): {
    RAnswers.Reply.ask(
      RAnswers.Versions.find.at(r, _)
    )
      == Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
  }
  %Equal.sym(
    Maybe<&2, Types.Entry>,
    List.get(&2, Types.Entry, r, j),
    Some{e},
    eg
  ): {
    RAnswers.Reply.ask(
      Maybe.map(&2, Types.Entry, RAnswers.Found, e2 => RAnswers.Found{j, e2}, _)
    )
      == Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
  }
  {==}

# Made.of_at, for the entry e of the version
def Made.of_at.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -r: Spec.Request,
  +e: Types.Entry,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  +eg: {List.get(&2, Types.Entry, store, j) == Some{e}: Maybe<&2, Types.Entry>},
  er: {Groups.Entry.request(e) == r: Spec.Request}
) -> Mirror.Made(s, Ledgers.Line{h, None{}}, j, RLines.Entry.id(e), r):
  (
    Version.make(s, h, store, j, e, ev, eg),
    Own.cast(
      Spec.Request,
      w => {
        Answers.Answer.of(
          s,
          Spec.Question.Request{Ledgers.Line{h, None{}}, RLines.Entry.id(e)}
        )
          == Some{Spec.Reply.Ask{w}}: Maybe<&2, Spec.Reply>
      },
      RAnswers.Entry.request(e),
      r,
      Equal.trans(
        Spec.Request,
        RAnswers.Entry.request(e),
        Groups.Entry.request(e),
        r,
        Entry.request_same(e),
        er
      ),
      Request.make(
        s,
        h,
        store,
        j,
        e,
        ev,
        eg,
        Versions.Line.versions_index(s, Ledgers.Line{h, None{}}, store, j, e)(ev)(eg)
      )
    )
  )

# a version of the versions store of a store, made by the request r, is the
# decision of a request that asked for r
def Made.of_at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -r: Spec.Request,
  ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  a: Groups.Groups.At(store, j, r)
) -> Exists(Ledgers.Id, i => Mirror.Made(s, Ledgers.Line{h, None{}}, j, i, r)):
  (+e, p) = a
  (eg, er) = p
  (RLines.Entry.id(e), Made.of_at.of(s, h, store, j, r, e, ev, eg, er))

# At.of_made, for the entry e of the version
def At.of_made.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +e: Types.Entry,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  +eg: {List.get(&2, Types.Entry, store, j) == Some{e}: Maybe<&2, Types.Entry>},
  ei: {RLines.Entry.id(e) == i: Ledgers.Id},
  e2: {
    Answers.Answer.of(
      s,
      Spec.Question.Request{Ledgers.Line{h, None{}}, i}
    )
      == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
  }
) -> {Groups.Entry.request(e) == r: Spec.Request}:
  Equal.trans(
    Spec.Request,
    Groups.Entry.request(e),
    RAnswers.Entry.request(e),
    r,
    Equal.sym(
      Spec.Request,
      RAnswers.Entry.request(e),
      Groups.Entry.request(e),
      Entry.request_same(e)
    ),
    Shared.Maybe.some_inj(
      Spec.Request,
      RAnswers.Entry.request(e),
      r,
      Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, Spec.Request>,
        Reply.ask_of,
        Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}},
        Some{Spec.Reply.Ask{r}},
        Own.cast(
          Maybe<&2, Types.Entry>,
          w => {
            RAnswers.Reply.ask(
              Maybe.map(&2, Types.Entry, RAnswers.Found, e3 => RAnswers.Found{j, e3}, w)
            )
              == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
          },
          List.get(&2, Types.Entry, store, j),
          Some{e},
          eg,
          Own.cast(
            Maybe<&2, Nat>,
            w => {
              RAnswers.Reply.ask(
                RAnswers.Versions.find.at(store, w)
              )
                == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
            },
            Lists.List.index(
              ~Types.Entry,
              ~Ledgers.Id,
              ~RLines.Entry.is_of,
              store,
              RLines.Entry.id(e)
            ),
            Some{j},
            Versions.Line.versions_index(s, Ledgers.Line{h, None{}}, store, j, e)(ev)(eg),
            Own.cast(
              Maybe<&2, List<&2, Types.Entry>>,
              w => {
                RAnswers.Reply.ask(
                  RAnswers.Line.find.of(RLines.Entry.id(e), w)
                )
                  == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
              },
              Lines.Store.versions(s, h),
              Some{store},
              ev,
              Own.cast(
                Ledgers.Id,
                w => {
                  RAnswers.Reply.ask(
                    RAnswers.Line.find.of(w, Lines.Store.versions(s, h))
                  )
                    == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
                },
                i,
                RLines.Entry.id(e),
                Equal.sym(Ledgers.Id, RLines.Entry.id(e), i, ei),
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
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(
    Types.Entry,
    e => {
      List.get(&2, Types.Entry, store, j) == Some{e}: Maybe<&2, Types.Entry>
    }
      & {RLines.Entry.id(e) == i: Ledgers.Id}
  ),
  e2: {
    Answers.Answer.of(
      s,
      Spec.Question.Request{Ledgers.Line{h, None{}}, i}
    )
      == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
  }
) -> Groups.Groups.At(store, j, r):
  (+e, q) = p
  (+eg, ei) = q
  (e, (eg, At.of_made.of(s, h, store, j, i, r, e, ev, eg, ei, e2)))

# a version of a store that is the decision of a request that asked for r is
# a version of its versions store made by r
def At.of_made(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  mk: Mirror.Made(s, Ledgers.Line{h, None{}}, j, i, r)
) -> Groups.Groups.At(store, j, r):
  (e1, e2) = mk
  At.of_made.open(
    s,
    h,
    store,
    j,
    i,
    r,
    ev,
    Reply.id_some(
      List.get(&2, Types.Entry, store, j),
      i
    )(
      Own.cast(
        Maybe<&2, List<&2, Types.Entry>>,
        w => {
          RAnswers.Reply.id(
            RLines.Line.at.of(w, j)
          )
            == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
        },
        Lines.Store.versions(s, h),
        Some{store},
        ev,
        e1
      )
    ),
    e2
  )

# the latest version of the store h up to m that decides r is a version of
# its versions store made by r, at most m
def At.of_latest(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -m: Nat,
  -r: Spec.Request,
  +ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  l: Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, r)
) -> Groups.Groups.At(store, j, r)
  & {Nat.is_le(j, m) == True{}: Bool}:
  (ex, le) = l
  (i, mk) = ex
  (At.of_made(s, h, store, j, i, r, ev, mk), le)

# a version of the versions store of the store h made by r, at most m, is one
# that decides r up to m
def Latest.of_at(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +store: List<&2, Types.Entry>,
  +j: Nat,
  -m: Nat,
  -r: Spec.Request,
  ev: {Lines.Store.versions(s, h) == Some{store}: Maybe<&2, List<&2, Types.Entry>>},
  p: Groups.Groups.At(store, j, r) & {Nat.is_le(j, m) == True{}: Bool}
) -> Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, r):
  (a, le) = p
  (Made.of_at(s, h, store, j, r, ev, a), le)

# The members of a group
# ----------------------

# Core.members_decided, from the latest Group among the versions r of the
# store
def Core.members_decided.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  -ms: List<&2, String>,
  +r: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(
    Nat,
    j => (
      Groups.Groups.At(r, j, Spec.Request.Group{h, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
    )
      & (
        @j2: Nat -> @ms2: List<
          &2,
          String> -> Groups.Groups.At(
          r,
          j2,
          Spec.Request.Group{h, g, ms2}
        ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
      )
  )
) -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    Ledgers.Line{h, None{}},
    j,
    m,
    Spec.Request.Group{h, g, ms}
  )
    & (
      @j2: Nat -> @ms2: List<
        &2,
        String> -> Mirror.Latest(
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
      Latest.of_at(s, h, r, j, m, Spec.Request.Group{h, g, ms}, ev, hit),
      +j2 => +ms2 => l => Groups.Pair.use(
        Groups.Groups.At(r, j2, Spec.Request.Group{h, g, ms2}),
        {Nat.is_le(j2, m) == True{}: Bool},
        {Nat.is_le(j2, j) == True{}: Bool},
        At.of_latest(s, h, r, j2, m, Spec.Request.Group{h, g, ms2}, ev, l),
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
  j => Mirror.Latest(
    s,
    Ledgers.Line{h, None{}},
    j,
    m,
    Spec.Request.Group{h, g, ms}
  )
    & (
      @j2: Nat -> @ms2: List<
        &2,
        String> -> Mirror.Latest(
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
def Core.members_decided(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ms: List<&2, String>
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Members{h, g, m}
  )
    == Some{Spec.Reply.Names{ms}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    Ledgers.Line{h, None{}},
    j,
    m,
    Spec.Request.Group{h, g, ms}
  )
    & (
      @j2: Nat -> @ms2: List<
        &2,
        String> -> Mirror.Latest(
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
# versions r of the store
def Core.groups_decided.yes(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +r: List<&2, Types.Entry>,
  ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(
    Nat,
    j => Exists(
      List<&2, String>,
      ms => Groups.Groups.At(r, j, Spec.Request.Group{h, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
    )
  )
) -> Exists(
  Nat,
  j => Exists(
    List<&2, String>,
    ms => Mirror.Latest(s, Ledgers.Line{h, None{}}, j, m, Spec.Request.Group{h, g, ms})
  )
):
  (+j, q) = p
  (ms, hit) = q
  (j, (ms, Latest.of_at(s, h, r, j, m, Spec.Request.Group{h, g, ms}, ev, hit)))

# Core.groups_decided, with the versions r of the store
def Core.groups_decided.of(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +y: Bool,
  +r: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, h) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  +ey: {Groups.Groups.is_group(r, h, g, m) == Some{y}: Maybe<&2, Bool>}
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
    } -> @j: Nat -> @ms: List<
      &2,
      String> -> Mirror.Latest(
      s,
      Ledgers.Line{h, None{}},
      j,
      m,
      Spec.Request.Group{h, g, ms}
    ) -> Empty
  ):
  (
    ty => Core.groups_decided.yes(
      s,
      h,
      g,
      m,
      r,
      ev,
      Groups.Groups.is_group_yes(
        r,
        h,
        g,
        m,
        Own.cast(
          Bool,
          w => {Groups.Groups.is_group(r, h, g, m) == Some{w}: Maybe<&2, Bool>},
          y,
          True{},
          ty,
          ey
        )
      )
    ),
    fy => +j => +ms => l => Groups.Pair.use(
      Groups.Groups.At(r, j, Spec.Request.Group{h, g, ms}),
      {Nat.is_le(j, m) == True{}: Bool},
      Empty,
      At.of_latest(s, h, r, j, m, Spec.Request.Group{h, g, ms}, ev, l),
      a => le => Groups.Groups.is_group_no(
        r,
        h,
        g,
        m,
        Own.cast(
          Bool,
          w => {Groups.Groups.is_group(r, h, g, m) == Some{w}: Maybe<&2, Bool>},
          y,
          False{},
          fy,
          ey
        )
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
    } -> @j: Nat -> @ms: List<
      &2,
      String> -> Mirror.Latest(
      s,
      Ledgers.Line{h, None{}},
      j,
      m,
      Spec.Request.Group{h, g, ms}
    ) -> Empty
  ):
  (+R, q) = p
  (ev, q2) = q
  (lt, ey) = q2
  Core.groups_decided.of(s, h, g, m, y, R, ev, ey)

# A name is a group at a version of the store exactly when a Group of that name
# was decided up to it.
def Core.groups_decided(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +g: String,
  +m: Nat,
  +y: Bool
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.IsGroup{h, g, m}
  )
    == Some{Spec.Reply.Yes{y}}: Maybe<&2, Spec.Reply>
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
    } -> @j: Nat -> @ms: List<
      &2,
      String> -> Mirror.Latest(
      s,
      Ledgers.Line{h, None{}},
      j,
      m,
      Spec.Request.Group{h, g, ms}
    ) -> Empty
  ):
  e => Core.groups_decided.open(s, h, g, m, y, IsGroup.some(s, h, g, m, y, e))

# The rule of a version
# ---------------------

# the name of the owner group of a rule, if the rule has one
def Rule.name_of(m: Maybe<&2, RLines.Rule>) -> Maybe<&2, String>:
  match m:
    case Some{RLines.Rule{Some{g}, ns}}:
      Some{g}
    case _:
      None{}

# the nodes of a rule
def Rule.nodes_of(m: Maybe<&2, RLines.Rule>) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{RLines.Rule{g, ns}}:
      Some{ns}
    case _:
      None{}

# a rule of the nodes of a named group is the rule of g and ns only for the
# name g and the nodes ns
def Rule.named_some(
  -name: String,
  n: Maybe<&2, List<&2, String>>,
  -g: String,
  -ns: List<&2, String>
) -> {
  Maybe.map(
    &2,
    List<&2, String>,
    RLines.Rule,
    ns2 => RLines.Rule{Some{name}, ns2},
    n
  )
    == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
} -> {name == g: String}
  & {n == Some{ns}: Maybe<&2, List<&2, String>>}:
  match n:
    case None{}:
      h => Empty.absurd(
        {name == g: String} & {None{} == Some{ns}: Maybe<&2, List<&2, String>>},
        Shared.Maybe.none_ne_some(RLines.Rule, RLines.Rule{Some{g}, ns}, h)
      )
    case Some{x}:
      +h => (
        Shared.Maybe.some_inj(
          String,
          name,
          g,
          Equal.cong(
            Maybe<&2, RLines.Rule>,
            Maybe<&2, String>,
            Rule.name_of,
            Some{RLines.Rule{Some{name}, x}},
            Some{RLines.Rule{Some{g}, ns}},
            h
          )
        ),
        Equal.cong(
          Maybe<&2, RLines.Rule>,
          Maybe<&2, List<&2, String>>,
          Rule.nodes_of,
          Some{RLines.Rule{Some{name}, x}},
          Some{RLines.Rule{Some{g}, ns}},
          h
        )
      )

# the rule of a store that named no owner group is the rule of no named group
def Rule.plain_none(
  b: Bool,
  -os: List<&2, String>,
  -g: String,
  -ns: List<&2, String>
) -> {
  Shared.Maybe.when(
    RLines.Rule,
    b,
    u => Some{RLines.Rule{None{}, os}}
  )
    == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
} -> Empty:
  match b:
    case True{}:
      h => Shared.Maybe.none_ne_some(
        String,
        g,
        Equal.cong(
          Maybe<&2, RLines.Rule>,
          Maybe<&2, String>,
          Rule.name_of,
          Some{RLines.Rule{None{}, os}},
          Some{RLines.Rule{Some{g}, ns}},
          h
        )
      )
    case False{}:
      h => Shared.Maybe.none_ne_some(RLines.Rule, RLines.Rule{Some{g}, ns}, h)

# Rule.of_some, for the owner group name
def Rule.of_some.at(
  -r: List<&2, Types.Entry>,
  -c: Ledgers.Line,
  -m: Nat,
  -name: String,
  -g: String,
  -ns: List<&2, String>,
  p: {
    name == g: String
  }
    & {
      Groups.Groups.nodes(r, RLines.Line.root(c), name, m) == Some{ns}: Maybe<&2, List<&2, String>>
    }
) -> {
  Some{name} == Some{g}: Maybe<&2, String>
}
  & {Groups.Groups.nodes(r, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>}:
  (+en, e_n) = p
  (
    Equal.cong(String, Maybe<&2, String>, w => Some{w}, name, g, en),
    Own.cast(
      String,
      w => {
        Groups.Groups.nodes(r, RLines.Line.root(c), w, m) == Some{ns}: Maybe<&2, List<&2, String>>
      },
      name,
      g,
      en,
      e_n
    )
  )

# a rule of the owner group g and the nodes ns: the owner group is g, and its
# nodes at the era are ns
def Rule.of_some(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  og: Maybe<&2, String>,
  -g: String,
  -ns: List<&2, String>
) -> {
  RLines.Rule.of(r, c, m, og) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
} -> {
  og == Some{g}: Maybe<&2, String>
}
  & {Groups.Groups.nodes(r, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>}:
  match og:
    case None{}:
      h => Empty.absurd(
        {
          None{} == Some{g}: Maybe<&2, String>
        }
          & {
            Groups.Groups.nodes(
              r,
              RLines.Line.root(c),
              g,
              m
            )
              == Some{ns}: Maybe<&2, List<&2, String>>
          },
        Rule.plain_none(RLines.Line.is_root(c), RLines.Store.owners(r), g, ns)(h)
      )
    case Some{+name}:
      h => Rule.of_some.at(
        r,
        c,
        m,
        name,
        g,
        ns,
        Rule.named_some(name, Groups.Groups.nodes(r, RLines.Line.root(c), name, m), g, ns)(h)
      )

# Rule.at_some, once the era is known to be a version of the store
def Rule.at_some.of(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -g: String,
  -ns: List<&2, String>,
  p: {
    Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool
  }
    & {
      RLines.Rule.of(
        r,
        c,
        m,
        Groups.Groups.owner(r, c, m)
      )
        == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
    }
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool
}
  & (
    {
      Groups.Groups.owner(r, c, m) == Some{g}: Maybe<&2, String>
    }
      & {Groups.Groups.nodes(r, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>}
  ):
  (lt, hr) = p
  (lt, Rule.of_some(r, c, m, Groups.Groups.owner(r, c, m), g, ns)(hr))

# the rule that the era m of the versions r of a store gives is of the owner
# group g and the nodes ns: m is a version of r, where the owner group of the
# line is g and its nodes are ns
def Rule.at_some(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -g: String,
  -ns: List<&2, String>,
  h: {RLines.Rule.at(r, c, m) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, r)) == True{}: Bool
}
  & (
    {
      Groups.Groups.owner(r, c, m) == Some{g}: Maybe<&2, String>
    }
      & {Groups.Groups.nodes(r, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>}
  ):
  Rule.at_some.of(
    r,
    c,
    m,
    g,
    ns,
    When.some(
      RLines.Rule,
      Nat.is_lt(m, List.length(&2, Types.Entry, r)),
      RLines.Rule.of(r, c, m, Groups.Groups.owner(r, c, m)),
      RLines.Rule{Some{g}, ns},
      h
    )
  )

# a number below n is, with one more, at most n
def Nat.lt_le_succ(
  a: Nat,
  n: Nat
) -> {Nat.is_lt(a, n) == True{}: Bool} -> {Nat.is_le(1n+a, n) == True{}: Bool}:
  match a n:
    case 0n 0n:
      h => h
    case 0n 1n+q:
      h => Shared.Nat.le_zero(q)
    case 1n+p 0n:
      h => h
    case 1n+p 1n+q:
      Nat.lt_le_succ(p, q)

# Rule.at_take, with the facts of the first versions
def Rule.at_take.of(
  +vs: List<&2, Types.Entry>,
  +j: Nat,
  -c: Ledgers.Line,
  +m: Nat,
  -g: String,
  -ns: List<&2, String>,
  p: {
    Nat.is_lt(m, List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, 1n+j))) == True{}: Bool
  }
    & (
      {
        Groups.Groups.owner(
          List.take(&2, Types.Entry, vs, 1n+j),
          c,
          m
        )
          == Some{g}: Maybe<&2, String>
      }
        & {
          Groups.Groups.nodes(
            List.take(&2, Types.Entry, vs, 1n+j),
            RLines.Line.root(c),
            g,
            m
          )
            == Some{ns}: Maybe<&2, List<&2, String>>
        }
    )
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, vs)) == True{}: Bool
}
  & (
    {
      Groups.Groups.owner(vs, c, m) == Some{g}: Maybe<&2, String>
    }
      & {
        Groups.Groups.nodes(vs, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>
      }
  ):
  (+lt, q) = p
  (eo, en) = q
  (
    Shared.Nat.lt_le(
      m,
      List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, 1n+j)),
      List.length(&2, Types.Entry, vs)
    )(
      lt
    )(
      Lists.List.ext_length(
        Types.Entry,
        List.take(&2, Types.Entry, vs, 1n+j),
        vs
      )(Lists.List.take_ext(Types.Entry, vs, 1n+j))
    ),
    (
      Equal.trans(
        Maybe<&2, String>,
        Groups.Groups.owner(vs, c, m),
        Groups.Groups.owner(List.take(&2, Types.Entry, vs, 1n+j), c, m),
        Some{g},
        Groups.Groups.owner_take(
          vs,
          List.take(&2, Types.Entry, vs, 1n+j),
          c,
          m,
          Lists.List.ext_take(
            Types.Entry,
            List.take(&2, Types.Entry, vs, 1n+j),
            vs,
            1n+m
          )(
            Lists.List.take_ext(Types.Entry, vs, 1n+j)
          )(
            Nat.lt_le_succ(
              m,
              List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, 1n+j))
            )(lt)
          )
        ),
        eo
      ),
      Equal.trans(
        Maybe<&2, List<&2, String>>,
        Groups.Groups.nodes(vs, RLines.Line.root(c), g, m),
        Groups.Groups.nodes(List.take(&2, Types.Entry, vs, 1n+j), RLines.Line.root(c), g, m),
        Some{ns},
        Groups.Groups.nodes_take(
          vs,
          List.take(&2, Types.Entry, vs, 1n+j),
          RLines.Line.root(c),
          g,
          m,
          Lists.List.ext_take(
            Types.Entry,
            List.take(&2, Types.Entry, vs, 1n+j),
            vs,
            1n+m
          )(
            Lists.List.take_ext(Types.Entry, vs, 1n+j)
          )(
            Nat.lt_le_succ(
              m,
              List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, 1n+j))
            )(lt)
          )
        ),
        en
      )
    )
  )

# what the era m of the first versions of a store gives as the rule, m gives
# of all the versions of the store
def Rule.at_take(
  +vs: List<&2, Types.Entry>,
  +j: Nat,
  +c: Ledgers.Line,
  +m: Nat,
  -g: String,
  -ns: List<&2, String>,
  h: {
    RLines.Rule.at(
      List.take(&2, Types.Entry, vs, 1n+j),
      c,
      m
    )
      == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
  }
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, vs)) == True{}: Bool
}
  & (
    {
      Groups.Groups.owner(vs, c, m) == Some{g}: Maybe<&2, String>
    }
      & {
        Groups.Groups.nodes(vs, RLines.Line.root(c), g, m) == Some{ns}: Maybe<&2, List<&2, String>>
      }
  ):
  Rule.at_take.of(
    vs,
    j,
    c,
    m,
    g,
    ns,
    Rule.at_some(List.take(&2, Types.Entry, vs, 1n+j), c, m, g, ns, h)
  )

# the store of the line c has versions R that reach m, where the owner group
# of c is g and its nodes are ns
def Owned(s: Facts.Facts(), c: Ledgers.Line, g: String, ns: List<&2, String>, m: Nat) -> Type:
  Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, Spec.Line.store(c)) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
        }
          & (
            {
              Groups.Groups.owner(R, c, m) == Some{g}: Maybe<&2, String>
            }
              & {
                Groups.Groups.nodes(
                  R,
                  Spec.Line.store(c),
                  g,
                  m
                )
                  == Some{ns}: Maybe<&2, List<&2, String>>
              }
          )
      )
  )

# Before.some, once the line is known to have the version
def Before.some.at(
  +j: Nat,
  +vs: List<&2, Types.Entry>,
  -prev: List<&2, Types.Entry>,
  p: {
    Nat.is_lt(j, List.length(&2, Types.Entry, vs)) == True{}: Bool
  }
    & {Some{List.take(&2, Types.Entry, vs, 1n+j)} == Some{prev}: Maybe<&2, List<&2, Types.Entry>>}
) -> Exists(
  List<&2, Types.Entry>,
  ws => {
    Some{vs} == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(j, List.length(&2, Types.Entry, ws)) == True{}: Bool
      }
        & {List.take(&2, Types.Entry, ws, 1n+j) == prev: List<&2, Types.Entry>}
    )
):
  (lt, e) = p
  (
    vs,
    (
      {==},
      (
        lt,
        Shared.Maybe.some_inj(List<&2, Types.Entry>, List.take(&2, Types.Entry, vs, 1n+j), prev, e)
      )
    )
  )

# the versions before version 1+j of a line are the first 1+j of its versions
def Before.some(
  +j: Nat,
  mv: Maybe<&2, List<&2, Types.Entry>>,
  -p: List<&2, Types.Entry>
) -> {
  RAnswers.Line.before.of(j, mv) == Some{p}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  ws => {
    mv == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
  }
    & (
      {
        Nat.is_lt(j, List.length(&2, Types.Entry, ws)) == True{}: Bool
      }
        & {List.take(&2, Types.Entry, ws, 1n+j) == p: List<&2, Types.Entry>}
    )
):
  match mv:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          ws => {
            None{} == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
          }
            & (
              {
                Nat.is_lt(j, List.length(&2, Types.Entry, ws)) == True{}: Bool
              }
                & {List.take(&2, Types.Entry, ws, 1n+j) == p: List<&2, Types.Entry>}
            )
        ),
        Shared.Maybe.none_ne_some(List<&2, Types.Entry>, p, h)
      )
    case Some{+vs}:
      h => Before.some.at(
        j,
        vs,
        p,
        When.some(
          List<&2, Types.Entry>,
          Nat.is_lt(j, List.length(&2, Types.Entry, vs)),
          Some{List.take(&2, Types.Entry, vs, 1n+j)},
          p,
          h
        )
      )

# the rule after the versions P of a branch is of a named group: the store of
# the branch has versions, and they give the rule at the era of P
def Rule.after.of_some(
  +c: Ledgers.Line,
  +p: List<&2, Types.Entry>,
  mv: Maybe<&2, List<&2, Types.Entry>>,
  -u: RLines.Rule
) -> {
  RLines.Rule.after.of(c, p, mv) == Some{u}: Maybe<&2, RLines.Rule>
} -> Exists(
  List<&2, Types.Entry>,
  R => {
    mv == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {RLines.Rule.at(R, c, RLines.Line.era(c, p)) == Some{u}: Maybe<&2, RLines.Rule>}
):
  match mv:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          R => {
            None{} == Some{R}: Maybe<&2, List<&2, Types.Entry>>
          }
            & {RLines.Rule.at(R, c, RLines.Line.era(c, p)) == Some{u}: Maybe<&2, RLines.Rule>}
        ),
        Shared.Maybe.none_ne_some(RLines.Rule, u, h)
      )
    case Some{+R}:
      h => (R, ({==}, h))

# Rule.after_some, for a branch, with the versions of its store
def Rule.after_some.branch(
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  -prev: List<&2, Types.Entry>,
  -g: String,
  -ns: List<&2, String>,
  +m: Nat,
  em: {RLines.Line.era(Ledgers.Line{h, Some{b}}, prev) == m: Nat},
  p: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Store.versions(s, h) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & {
        RLines.Rule.at(
          R,
          Ledgers.Line{h, Some{b}},
          RLines.Line.era(Ledgers.Line{h, Some{b}}, prev)
        )
          == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
      }
  )
) -> Owned(s, Ledgers.Line{h, Some{b}}, g, ns, m):
  (+R, q) = p
  (ev, ea) = q
  (
    R,
    (
      ev,
      Rule.at_some(
        R,
        Ledgers.Line{h, Some{b}},
        m,
        g,
        ns,
        Own.cast(
          Nat,
          w => {
            RLines.Rule.at(
              R,
              Ledgers.Line{h, Some{b}},
              w
            )
              == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
          },
          RLines.Line.era(Ledgers.Line{h, Some{b}}, prev),
          m,
          em,
          ea
        )
      )
    )
  )

# the rule after the first 1+j versions P of the line c, of the era m, is of
# the owner group g and the nodes ns: the store of c gives them at m
def Rule.after_some(
  +s: Facts.Facts(),
  c: Ledgers.Line,
  +p: List<&2, Types.Entry>,
  -g: String,
  -ns: List<&2, String>,
  +m: Nat,
  +vs: List<&2, Types.Entry>,
  +j: Nat
) -> {
  Lines.Rule.after(s, c, p) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
} -> {
  RLines.Line.era(c, p) == m: Nat
} -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.take(&2, Types.Entry, vs, 1n+j) == p: List<&2, Types.Entry>} -> Owned(s, c, g, ns, m):
  match c:
    case Ledgers.Line{+h, None{}}:
      ea => em => ev => ep => (
        vs,
        (
          ev,
          Rule.at_take(
            vs,
            j,
            Ledgers.Line{h, None{}},
            m,
            g,
            ns,
            Own.cast(
              List<&2, Types.Entry>,
              w => {
                RLines.Rule.at(
                  w,
                  Ledgers.Line{h, None{}},
                  m
                )
                  == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
              },
              p,
              List.take(&2, Types.Entry, vs, 1n+j),
              Equal.sym(List<&2, Types.Entry>, List.take(&2, Types.Entry, vs, 1n+j), p, ep),
              Own.cast(
                Nat,
                w => {
                  RLines.Rule.at(
                    p,
                    Ledgers.Line{h, None{}},
                    w
                  )
                    == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
                },
                RLines.Line.era(Ledgers.Line{h, None{}}, p),
                m,
                em,
                ea
              )
            )
          )
        )
      )
    case Ledgers.Line{+h, Some{+b}}:
      ea => em => ev => ep => Rule.after_some.branch(
        s,
        h,
        b,
        p,
        g,
        ns,
        m,
        em,
        Rule.after.of_some(
          Ledgers.Line{h, Some{b}},
          p,
          Lines.Store.versions(s, h),
          RLines.Rule{Some{g}, ns}
        )(ea)
      )

# Rule.for_some, with the versions P before the version, once the line is
# known to have them
def Rule.for_some.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +j: Nat,
  -g: String,
  -ns: List<&2, String>,
  +m: Nat,
  +prev: List<&2, Types.Entry>,
  ea: {Lines.Rule.after(s, c, prev) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>},
  em: {RLines.Line.era(c, prev) == m: Nat},
  p: Exists(
    List<&2, Types.Entry>,
    ws => {
      Lines.Line.versions(s, c) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
    }
      & (
        {
          Nat.is_lt(j, List.length(&2, Types.Entry, ws)) == True{}: Bool
        }
          & {List.take(&2, Types.Entry, ws, 1n+j) == prev: List<&2, Types.Entry>}
      )
  )
) -> Owned(s, c, g, ns, m):
  (+vs, q) = p
  (ev, q2) = q
  (lt, ep) = q2
  Rule.after_some(s, c, prev, g, ns, m, vs, j)(ea)(em)(ev)(ep)

# the rule of version k of the line c is of the owner group g and the nodes
# ns, and its era is m: the store of c has versions that reach m, where the
# owner group of c is g and its nodes are ns
def Rule.for_some(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  -g: String,
  -ns: List<&2, String>,
  +m: Nat
) -> {
  Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
} -> {Answers.Era.for(s, c, k) == Some{m}: Maybe<&2, Nat>} -> Owned(s, c, g, ns, m):
  match k:
    case 0n:
      h1 => h2 => Empty.absurd(Owned(s, c, g, ns, m), Shared.Maybe.none_ne_some(Nat, m, h2))
    case 1n+j:
      +j = j
      Lists.Maybe.by(
        List<&2, Types.Entry>,
        mb => {
          Answers.Rule.for.of(s, c, mb) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
        } -> {
          Maybe.map(
            &2,
            List<&2, Types.Entry>,
            Nat,
            vs => RLines.Line.era(c, vs),
            mb
          )
            == Some{m}: Maybe<&2, Nat>
        } -> Owned(s, c, g, ns, m),
        Answers.Line.before(s, c, j),
        eb => h1 => h2 => Empty.absurd(
          Owned(s, c, g, ns, m),
          Shared.Maybe.none_ne_some(Nat, m, h2)
        ),
        +P => eb => h1 => h2 => Rule.for_some.of(
          s,
          c,
          j,
          g,
          ns,
          m,
          P,
          h1,
          Shared.Maybe.some_inj(Nat, RLines.Line.era(c, P), m, h2),
          Before.some(j, Lines.Line.versions(s, c), P)(eb)
        )
      )

# The owner group of a line
# -------------------------

# a reply of the name g of the owner group of a rule comes from a rule of the
# owner group g
def Owner.some(
  u: Maybe<&2, RLines.Rule>,
  -g: String
) -> {
  Maybe.bind(
    &2,
    RLines.Rule,
    Spec.Reply,
    u,
    RAnswers.Rule.owner
  )
    == Some{Spec.Reply.Name{g}}: Maybe<&2, Spec.Reply>
} -> Exists(List<&2, String>, ns => {u == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}):
  match u:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, String>,
          ns => {None{} == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Name{g}, h)
      )
    case Some{RLines.Rule{None{}, ns}}:
      h => Empty.absurd(
        Exists(
          List<&2, String>,
          ns2 => {
            Some{RLines.Rule{None{}, ns}} == Some{RLines.Rule{Some{g}, ns2}}: Maybe<&2, RLines.Rule>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Name{g}, h)
      )
    case Some{RLines.Rule{Some{g2}, +ns}}:
      h => (
        ns,
        Equal.cong(
          String,
          Maybe<&2, RLines.Rule>,
          w => Some{RLines.Rule{Some{w}, ns}},
          g2,
          g,
          Shared.Maybe.some_inj(
            String,
            g2,
            g,
            Equal.cong(
              Maybe<&2, Spec.Reply>,
              Maybe<&2, String>,
              Reply.name_of,
              Some{Spec.Reply.Name{g2}},
              Some{Spec.Reply.Name{g}},
              h
            )
          )
        )
      )

# a reply of the names gs of the nodes of a rule comes from a rule of a named
# owner group and the nodes gs
def Group.some(
  u: Maybe<&2, RLines.Rule>,
  -gs: List<&2, String>
) -> {
  Maybe.bind(
    &2,
    RLines.Rule,
    Spec.Reply,
    u,
    RAnswers.Rule.group
  )
    == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
} -> Exists(String, g => {u == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>}):
  match u:
    case None{}:
      h => Empty.absurd(
        Exists(String, g => {None{} == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>}),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{gs}, h)
      )
    case Some{RLines.Rule{None{}, ns}}:
      h => Empty.absurd(
        Exists(
          String,
          g => {
            Some{RLines.Rule{None{}, ns}} == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{gs}, h)
      )
    case Some{RLines.Rule{Some{+g2}, ns}}:
      h => (
        g2,
        Equal.cong(
          List<&2, String>,
          Maybe<&2, RLines.Rule>,
          w => Some{RLines.Rule{Some{g2}, w}},
          ns,
          gs,
          Shared.Maybe.some_inj(
            List<&2, String>,
            ns,
            gs,
            Equal.cong(
              Maybe<&2, Spec.Reply>,
              Maybe<&2, List<&2, String>>,
              Reply.names_of,
              Some{Spec.Reply.Names{ns}},
              Some{Spec.Reply.Names{gs}},
              h
            )
          )
        )
      )

# Core.owner_decided, from the latest Own among the versions r of the store
def Core.owner_decided.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  -g: String,
  +m: Nat,
  +r: List<&2, Types.Entry>,
  +ev: {Lines.Store.versions(s, Spec.Line.store(c)) == Some{r}: Maybe<&2, List<&2, Types.Entry>>},
  p: Exists(
    Nat,
    j => (
      Groups.Groups.At(r, j, Spec.Request.Own{c, g}) & {Nat.is_le(j, m) == True{}: Bool}
    )
      & (
        @j2: Nat -> @g2: String -> Groups.Groups.At(
          r,
          j2,
          Spec.Request.Own{c, g2}
        ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
      )
  )
) -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    c,
    j,
    m,
    Spec.Request.Own{c, g}
  )
    & (
      @j2: Nat -> @g2: String -> Mirror.Latest(
        s,
        c,
        j2,
        m,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+j, q) = p
  (hit, later) = q
  (
    j,
    (
      Latest.of_at(s, Spec.Line.store(c), r, j, m, Spec.Request.Own{c, g}, ev, hit),
      +j2 => +g2 => l => Groups.Pair.use(
        Groups.Groups.At(r, j2, Spec.Request.Own{c, g2}),
        {Nat.is_le(j2, m) == True{}: Bool},
        {Nat.is_le(j2, j) == True{}: Bool},
        At.of_latest(s, Spec.Line.store(c), r, j2, m, Spec.Request.Own{c, g2}, ev, l),
        a => le => later(j2)(g2)(a)(le)
      )
    )
  )

# Core.owner_decided, from what the store of the line gives at the era
def Core.owner_decided.open(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +g: String,
  -ns: List<&2, String>,
  +m: Nat,
  p: Owned(s, c, g, ns, m)
) -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    c,
    j,
    m,
    Spec.Request.Own{c, g}
  )
    & (
      @j2: Nat -> @g2: String -> Mirror.Latest(
        s,
        c,
        j2,
        m,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+R, q) = p
  (ev, q2) = q
  (lt, q3) = q2
  (eo, en) = q3
  Core.owner_decided.of(s, c, g, m, R, ev, Groups.Groups.owner_latest(R, c, m, g, eo))

# Core.owner_decided, once the rule of the version is known
def Core.owner_decided.rule(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +g: String,
  +m: Nat,
  e2: {
    Answers.Answer.of(
      s,
      Spec.Question.Era{c, k}
    )
      == Some{Spec.Reply.Number{m}}: Maybe<&2, Spec.Reply>
  },
  p: Exists(
    List<&2, String>,
    ns => {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}
  )
) -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    c,
    j,
    m,
    Spec.Request.Own{c, g}
  )
    & (
      @j2: Nat -> @g2: String -> Mirror.Latest(
        s,
        c,
        j2,
        m,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (ns, er) = p
  Core.owner_decided.open(
    s,
    c,
    g,
    ns,
    m,
    Rule.for_some(s, c, k, g, ns, m)(er)(Reply.number_some(Answers.Era.for(s, c, k), m)(e2))
  )

# The owner group of a line is the one that the latest Own of the line, up to
# the era, names.
def Core.owner_decided(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +g: String,
  +m: Nat
) -> {
  Answers.Answer.of(s, Spec.Question.Owner{c, k}) == Some{Spec.Reply.Name{g}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Era{c, k}) == Some{Spec.Reply.Number{m}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  j => Mirror.Latest(
    s,
    c,
    j,
    m,
    Spec.Request.Own{c, g}
  )
    & (
      @j2: Nat -> @g2: String -> Mirror.Latest(
        s,
        c,
        j2,
        m,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  e1 => e2 => Core.owner_decided.rule(
    s,
    c,
    k,
    g,
    m,
    e2,
    Owner.some(Answers.Rule.for(s, c, k), g)(e1)
  )

# The group that decides a version
# --------------------------------

# a version that has a rule has an era
def Era.some(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  -u: RLines.Rule
) -> {
  Answers.Rule.for(s, c, k) == Some{u}: Maybe<&2, RLines.Rule>
} -> Exists(Nat, m => {Answers.Era.for(s, c, k) == Some{m}: Maybe<&2, Nat>}):
  match k:
    case 0n:
      h => Empty.absurd(
        Exists(Nat, m => {None{} == Some{m}: Maybe<&2, Nat>}),
        Shared.Maybe.none_ne_some(RLines.Rule, u, h)
      )
    case 1n+j:
      +j = j
      Lists.Maybe.by(
        List<&2, Types.Entry>,
        mb => {
          Answers.Rule.for.of(s, c, mb) == Some{u}: Maybe<&2, RLines.Rule>
        } -> Exists(
          Nat,
          m => {
            Maybe.map(
              &2,
              List<&2, Types.Entry>,
              Nat,
              vs => RLines.Line.era(c, vs),
              mb
            )
              == Some{m}: Maybe<&2, Nat>
          }
        ),
        Answers.Line.before(s, c, j),
        eb => h => Empty.absurd(
          Exists(Nat, m => {None{} == Some{m}: Maybe<&2, Nat>}),
          Shared.Maybe.none_ne_some(RLines.Rule, u, h)
        ),
        +P => eb => h => (RLines.Line.era(c, P), {==})
      )

# Core.group_of_era, from what the store of the line gives at the era
def Core.group_of_era.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>,
  +g: String,
  +m: Nat,
  er: {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>},
  em: {Answers.Era.for(s, c, k) == Some{m}: Maybe<&2, Nat>},
  p: Owned(s, c, g, gs, m)
) -> Exists(
  String,
  g2 => Exists(
    Nat,
    m2 => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g2}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m2}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g2, m2}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  (R, q) = p
  (ev, q2) = q
  (lt, q3) = q2
  (eo, en) = q3
  (
    g,
    (
      m,
      (
        Equal.cong(
          Maybe<&2, RLines.Rule>,
          Maybe<&2, Spec.Reply>,
          w => Maybe.bind(&2, RLines.Rule, Spec.Reply, w, RAnswers.Rule.owner),
          Answers.Rule.for(s, c, k),
          Some{RLines.Rule{Some{g}, gs}},
          er
        ),
        (
          Equal.cong(
            Maybe<&2, Nat>,
            Maybe<&2, Spec.Reply>,
            RAnswers.Reply.number,
            Answers.Era.for(s, c, k),
            Some{m},
            em
          ),
          Nodes.make(s, Spec.Line.store(c), g, m, R, gs, ev, lt, en)
        )
      )
    )
  )

# Core.group_of_era, with the rule and the era of the version
def Core.group_of_era.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>,
  +g: String,
  +m: Nat,
  +er: {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>},
  +em: {Answers.Era.for(s, c, k) == Some{m}: Maybe<&2, Nat>}
) -> Exists(
  String,
  g2 => Exists(
    Nat,
    m2 => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g2}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m2}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g2, m2}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  Core.group_of_era.of(s, c, k, gs, g, m, er, em, Rule.for_some(s, c, k, g, gs, m)(er)(em))

# Core.group_of_era, once the era of the version is known
def Core.group_of_era.era(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>,
  +g: String,
  +er: {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>},
  p: Exists(Nat, m => {Answers.Era.for(s, c, k) == Some{m}: Maybe<&2, Nat>})
) -> Exists(
  String,
  g2 => Exists(
    Nat,
    m2 => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g2}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m2}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g2, m2}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  (+m, em) = p
  Core.group_of_era.at(s, c, k, gs, g, m, er, em)

# Core.group_of_era, with the rule of the version
def Core.group_of_era.named(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>,
  +g: String,
  +er: {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>}
) -> Exists(
  String,
  g2 => Exists(
    Nat,
    m2 => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g2}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m2}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g2, m2}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  Core.group_of_era.era(s, c, k, gs, g, er, Era.some(s, c, k, RLines.Rule{Some{g}, gs})(er))

# Core.group_of_era, once the rule of the version is known
def Core.group_of_era.rule(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>,
  p: Exists(
    String,
    g => {Answers.Rule.for(s, c, k) == Some{RLines.Rule{Some{g}, gs}}: Maybe<&2, RLines.Rule>}
  )
) -> Exists(
  String,
  g2 => Exists(
    Nat,
    m2 => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g2}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m2}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g2, m2}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  (+g, er) = p
  Core.group_of_era.named(s, c, k, gs, g, er)

# The group that decides a version is the owner group of the line, made of its
# nodes at one version of the store: its era.
def Core.group_of_era(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +gs: List<&2, String>
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Group{c, k}
  )
    == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
} -> Exists(
  String,
  g => Exists(
    Nat,
    m => {
      Answers.Answer.of(
        s,
        Spec.Question.Owner{c, k}
      )
        == Some{Spec.Reply.Name{g}}: Maybe<&2, Spec.Reply>
    }
      & (
        {
          Answers.Answer.of(
            s,
            Spec.Question.Era{c, k}
          )
            == Some{Spec.Reply.Number{m}}: Maybe<&2, Spec.Reply>
        }
          & {
            Answers.Answer.of(
              s,
              Spec.Question.Nodes{Spec.Line.store(c), g, m}
            )
              == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
          }
      )
  )
):
  e => Core.group_of_era.rule(s, c, k, gs, Group.some(Answers.Rule.for(s, c, k), gs)(e))

# Eras never go back
# ------------------

# the greater of a and x is at most the greater of a and y, when x is at most y
def Nat.max_le_right(
  +a: Nat,
  +x: Nat,
  +y: Nat
) -> {Nat.is_le(x, y) == True{}: Bool} -> {Nat.is_le(Nat.max(a, x), Nat.max(a, y)) == True{}: Bool}:
  match a x y:
    case 0n v w:
      h => h
    case 1n+p 0n 0n:
      h => Shared.Nat.le_refl(p)
    case 1n+p 0n 1n+q:
      h => Lists.Nat.le_max_left(p, q)
    case 1n+p 1n+v 0n:
      h => Empty.absurd({Nat.is_le(Nat.max(p, v), p) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+v 1n+q:
      Nat.max_le_right(p, v, q)

# one less than a is at most one less than b, when a is at most b
def Nat.pred_le(
  +a: Nat,
  +b: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {Nat.is_le(Nat.sub(a, 1n), Nat.sub(b, 1n)) == True{}: Bool}:
  match a b:
    case 0n w:
      h => Shared.Nat.le_zero(Nat.sub(w, 1n))
    case 1n+p 0n:
      h => Empty.absurd(
        {Nat.is_le(Nat.sub(p, 0n), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case 1n+p 1n+q:
      h => (
        %Equal.sym(Nat, Nat.sub(p, 0n), p, Shared.Nat.sub_zero(p)): {Nat.is_le(_, Nat.sub(q, 0n)) == True{}: Bool}
        %Equal.sym(Nat, Nat.sub(q, 0n), q, Shared.Nat.sub_zero(q)): {Nat.is_le(p, _) == True{}: Bool}
        h)

# the first a of a list are no more than its first b, when a is at most b
def Take.length_le(
  +vs: List<&2, Types.Entry>,
  +a: Nat,
  +b: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Nat.is_le(
    List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, a)),
    List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, b))
  )
    == True{}: Bool
}:
  match vs a b:
    case Nil{} p q:
      h => {==}
    case Con{x, t} 0n q:
      h => Shared.Nat.le_zero(List.length(&2, Types.Entry, List.take(&2, Types.Entry, x <> t, q)))
    case Con{x, t} 1n+p 0n:
      h => Empty.absurd(
        {
          Nat.is_le(
            1n+List.length(&2, Types.Entry, List.take(&2, Types.Entry, t, p)),
            0n
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{x, t} 1n+p 1n+q:
      Take.length_le(t, p, q)

# the greatest era of the first a of a list is at most that of its first b,
# when a is at most b
def Take.peak_le(
  +vs: List<&2, Types.Entry>,
  +a: Nat,
  +b: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Nat.is_le(
    Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, vs, a)),
    Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, vs, b))
  )
    == True{}: Bool
}:
  match vs a b:
    case Nil{} p q:
      h => {==}
    case Con{x, t} 0n q:
      h => Shared.Nat.le_zero(
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, x <> t, q))
      )
    case Con{x, t} 1n+p 0n:
      h => Empty.absurd(
        {
          Nat.is_le(
            Nat.max(
              RLines.Entry.era(x),
              Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, t, p))
            ),
            0n
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{x, t} 1n+p 1n+q:
      h => Nat.max_le_right(
        RLines.Entry.era(x),
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, t, p)),
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.take(&2, Types.Entry, t, q))
      )(Take.peak_le(t, p, q)(h))

# the era after the first a versions of a line is at most that after its
# first b, when a is at most b
def Era.take_le(
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +a: Nat,
  +b: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Nat.is_le(
    RLines.Line.era(c, List.take(&2, Types.Entry, vs, a)),
    RLines.Line.era(c, List.take(&2, Types.Entry, vs, b))
  )
    == True{}: Bool
}:
  match c:
    case Ledgers.Line{r, None{}}:
      h => Nat.pred_le(
        List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, a)),
        List.length(&2, Types.Entry, List.take(&2, Types.Entry, vs, b))
      )(Take.length_le(vs, a, b)(h))
    case Ledgers.Line{r, Some{br}}:
      Take.peak_le(vs, a, b)

# Era.at, once the line is known to have the version (b)
def Era.at.if(
  -c: Ledgers.Line,
  b: Bool,
  -p: List<&2, Types.Entry>,
  -x: Nat
) -> {
  Maybe.map(
    &2,
    List<&2, Types.Entry>,
    Nat,
    vs => RLines.Line.era(c, vs),
    Shared.Maybe.when(List<&2, Types.Entry>, b, u => Some{p})
  )
    == Some{x}: Maybe<&2, Nat>
} -> {RLines.Line.era(c, p) == x: Nat}:
  match b:
    case True{}:
      h => Shared.Maybe.some_inj(Nat, RLines.Line.era(c, p), x, h)
    case False{}:
      h => Empty.absurd({RLines.Line.era(c, p) == x: Nat}, Shared.Maybe.none_ne_some(Nat, x, h))

# the era of version 1+i of a line: the line has versions, and it is the era
# after the first 1+i of them
def Era.at(
  +c: Ledgers.Line,
  +i: Nat,
  mv: Maybe<&2, List<&2, Types.Entry>>,
  -x: Nat
) -> {
  Maybe.map(
    &2,
    List<&2, Types.Entry>,
    Nat,
    vs => RLines.Line.era(c, vs),
    RAnswers.Line.before.of(i, mv)
  )
    == Some{x}: Maybe<&2, Nat>
} -> Exists(
  List<&2, Types.Entry>,
  ws => {
    mv == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {RLines.Line.era(c, List.take(&2, Types.Entry, ws, 1n+i)) == x: Nat}
):
  match mv:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          ws => {
            None{} == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
          }
            & {RLines.Line.era(c, List.take(&2, Types.Entry, ws, 1n+i)) == x: Nat}
        ),
        Shared.Maybe.none_ne_some(Nat, x, h)
      )
    case Some{+vs}:
      h => (
        vs,
        (
          {==},
          Era.at.if(
            c,
            Nat.is_lt(i, List.length(&2, Types.Entry, vs)),
            List.take(&2, Types.Entry, vs, 1n+i),
            x
          )(h)
        )
      )

# Era.grow, with the versions of the line as each era gives them
def Era.grow.of(
  +c: Ledgers.Line,
  +i: Nat,
  +j: Nat,
  -mv: Maybe<&2, List<&2, Types.Entry>>,
  -x: Nat,
  -y: Nat,
  l: {Nat.is_le(i, j) == True{}: Bool},
  p: Exists(
    List<&2, Types.Entry>,
    ws => {
      mv == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
    }
      & {RLines.Line.era(c, List.take(&2, Types.Entry, ws, 1n+i)) == x: Nat}
  ),
  q: Exists(
    List<&2, Types.Entry>,
    ws => {
      mv == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
    }
      & {RLines.Line.era(c, List.take(&2, Types.Entry, ws, 1n+j)) == y: Nat}
  )
) -> {Nat.is_le(x, y) == True{}: Bool}:
  (+vs, p2) = p
  (ev, ex) = p2
  (ws, q2) = q
  (ew, ey) = q2
  %ex: {Nat.is_le(_, y) == True{}: Bool}
  %ey: {Nat.is_le(RLines.Line.era(c, List.take(&2, Types.Entry, vs, 1n+i)), _) == True{}: Bool}
  %Shared.Maybe.some_inj(
    List<&2, Types.Entry>,
    vs,
    ws,
    Equal.trans(
      Maybe<&2, List<&2, Types.Entry>>,
      Some{vs},
      mv,
      Some{ws},
      Equal.sym(Maybe<&2, List<&2, Types.Entry>>, mv, Some{vs}, ev),
      ew
    )
  ): {
    Nat.is_le(
      RLines.Line.era(c, List.take(&2, Types.Entry, vs, 1n+i)),
      RLines.Line.era(c, List.take(&2, Types.Entry, _, 1n+j))
    )
      == True{}: Bool
  }
  Era.take_le(c, vs, 1n+i, 1n+j)(l)

# the era of a version of a line is at most the era of a later version
def Era.grow(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  a: Nat,
  b: Nat,
  -x: Nat,
  -y: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Answers.Era.for(s, c, a) == Some{x}: Maybe<&2, Nat>
} -> {Answers.Era.for(s, c, b) == Some{y}: Maybe<&2, Nat>} -> {Nat.is_le(x, y) == True{}: Bool}:
  match a b:
    case 0n q:
      l => e1 => e2 => Empty.absurd(
        {Nat.is_le(x, y) == True{}: Bool},
        Shared.Maybe.none_ne_some(Nat, x, e1)
      )
    case 1n+i 0n:
      l => e1 => e2 => Empty.absurd(
        {Nat.is_le(x, y) == True{}: Bool},
        Shared.Maybe.none_ne_some(Nat, y, e2)
      )
    case 1n+i 1n+j:
      +i = i
      +j = j
      l => e1 => e2 => Era.grow.of(
        c,
        i,
        j,
        Lines.Line.versions(s, c),
        x,
        y,
        l,
        Era.at(c, i, Lines.Line.versions(s, c), x)(e1),
        Era.at(c, j, Lines.Line.versions(s, c), y)(e2)
      )

# Eras never go back: a later version of a line is decided by groups of the
# same or a later version of the store.
def Core.eras_grow(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +x: Nat,
  +y: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Answers.Answer.of(s, Spec.Question.Era{c, a}) == Some{Spec.Reply.Number{x}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Era{c, b}) == Some{Spec.Reply.Number{y}}: Maybe<&2, Spec.Reply>
} -> {Nat.is_le(x, y) == True{}: Bool}:
  l => e1 => e2 => Era.grow(
    s,
    c,
    a,
    b,
    x,
    y
  )(
    l
  )(
    Reply.number_some(Answers.Era.for(s, c, a), x)(e1)
  )(Reply.number_some(Answers.Era.for(s, c, b), y)(e2))
