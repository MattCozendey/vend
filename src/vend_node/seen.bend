import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# The state of a line, as a node keeps it: laws
# ---------------------------------------------
# A node keeps the versions of a line the newest first, with their count
# (RKnown.Seen), so a new version is one more item. The defs that read a
# line through the table read what the node keeps when the table holds it,
# and else do what they did before. Here: each such read is the read that
# it replaces, of the versions the oldest first (RKnown.Seen.state).

# Versions, the last first
# ------------------------

# the items of xs, the last first, before acc, are as many as xs and acc
def Rev.go_length(xs: List<&2, Types.Entry>, +acc: List<&2, Types.Entry>) -> {
  List.length(&2, Types.Entry, List.reverse.go(&2, Types.Entry, xs, acc))
    == Nat.add(List.length(&2, Types.Entry, xs), List.length(&2, Types.Entry, acc)): Nat
}:
  match xs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      +tail = tail
      %Equal.sym(Nat, List.length(&2, Types.Entry, List.reverse.go(&2, Types.Entry, tail, head <> acc)), Nat.add(List.length(&2, Types.Entry, tail), List.length(&2, Types.Entry, head <> acc)), Rev.go_length(tail, head <> acc)) :
        {_ == 1n+Nat.add(List.length(&2, Types.Entry, tail), List.length(&2, Types.Entry, acc)) : Nat}
      Shared.Nat.add_succ(List.length(&2, Types.Entry, tail), List.length(&2, Types.Entry, acc))

# versions, the last first, are as many
def Rev.length(+xs: List<&2, Types.Entry>) -> {
  List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, xs)) == List.length(&2, Types.Entry, xs): Nat
}:
  Equal.trans(
    Nat,
    List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, xs)),
    Nat.add(List.length(&2, Types.Entry, xs), 0n),
    List.length(&2, Types.Entry, xs),
    Rev.go_length(xs, []),
    Shared.Nat.add_zero(List.length(&2, Types.Entry, xs))
  )

# the items of xs before acc, the last first, then the last first again
# before zs, are the items of acc, the last first, before xs and zs
def Rev.go_go(xs: List<&2, Types.Entry>, +acc: List<&2, Types.Entry>, -zs: List<&2, Types.Entry>) -> {
  List.reverse.go(&2, Types.Entry, List.reverse.go(&2, Types.Entry, xs, acc), zs)
    == List.reverse.go(&2, Types.Entry, acc, List.append(&2, Types.Entry, xs, zs)): List<&2, Types.Entry>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      %Equal.sym(List<&2, Types.Entry>, List.reverse.go(&2, Types.Entry, List.reverse.go(&2, Types.Entry, tail, head <> acc), zs), List.reverse.go(&2, Types.Entry, head <> acc, List.append(&2, Types.Entry, tail, zs)), Rev.go_go(tail, head <> acc, zs)) :
        {_ == List.reverse.go(&2, Types.Entry, acc, head <> List.append(&2, Types.Entry, tail, zs)) : List<&2, Types.Entry>}
      {==}

# versions, the last first, and then the last first again, are the versions
def Rev.twice(+xs: List<&2, Types.Entry>) -> {
  List.reverse(&2, Types.Entry, List.reverse(&2, Types.Entry, xs)) == xs: List<&2, Types.Entry>
}:
  Equal.trans(
    List<&2, Types.Entry>,
    List.reverse(&2, Types.Entry, List.reverse(&2, Types.Entry, xs)),
    List.append(&2, Types.Entry, xs, []),
    xs,
    Rev.go_go(xs, [], []),
    Shared.List.append_nil(Types.Entry, xs)
  )

# the items of xs, the last first, before acc, are xs, the last first, and
# then acc
def Rev.go_append(xs: List<&2, Types.Entry>, +acc: List<&2, Types.Entry>) -> {
  List.reverse.go(&2, Types.Entry, xs, acc)
    == List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, xs), acc): List<&2, Types.Entry>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(
        List<&2, Types.Entry>,
        List.reverse.go(&2, Types.Entry, t, h <> acc),
        List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, t), h <> acc),
        List.append(&2, Types.Entry, List.reverse.go(&2, Types.Entry, t, [h]), acc),
        Rev.go_append(t, h <> acc),
        (
          %Equal.sym(List<&2, Types.Entry>, List.reverse.go(&2, Types.Entry, t, [h]), List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, t), [h]), Rev.go_append(t, [h])): {List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, t), h <> acc) == List.append(&2, Types.Entry, _, acc): List<&2, Types.Entry>}
          Equal.sym(
            List<&2, Types.Entry>,
            List.append(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, t), [h]), acc),
            List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, t), h <> acc),
            Shared.List.append_assoc(Types.Entry, List.reverse(&2, Types.Entry, t), [h], acc)
          ))
      )

# a version before others, the last first, is the others, the last first,
# and then the version
def Rev.cons(+e: Types.Entry, +rest: List<&2, Types.Entry>) -> {
  List.reverse(&2, Types.Entry, e <> rest)
    == List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, rest), [e]): List<&2, Types.Entry>
}:
  Rev.go_append(rest, [e])

# e when it is the item asked for (hit), else m
def Snoc.pick(hit: Bool, e: Types.Entry, m: Maybe<&2, Types.Entry>) -> Maybe<&2, Types.Entry>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      m

# item k of ys and then e: e, when ys has k items; else item k of ys
def Snoc.get(ys: List<&2, Types.Entry>, +e: Types.Entry, k: Nat) -> {
  List.get(&2, Types.Entry, List.append(&2, Types.Entry, ys, [e]), k)
    == Snoc.pick(Nat.is_eq(List.length(&2, Types.Entry, ys), k), e, List.get(&2, Types.Entry, ys, k)): Maybe<&2, Types.Entry>
}:
  match ys k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{y, yt} 0n:
      {==}
    case Con{y, yt} 1n+p:
      Snoc.get(yt, e, p)

# a search of version k from the newest version on finds item k of the
# versions, the oldest first
def Rev.seek_eq(rest: List<&2, Types.Entry>, +e: Types.Entry, +k: Nat) -> {
  RKnown.Rev.seek(rest, Nat.is_eq(List.length(&2, Types.Entry, rest), k), e, List.length(&2, Types.Entry, rest), k)
    == List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, rest), [e]), k): Maybe<&2, Types.Entry>
}:
  match rest:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case Con{+e2, +r2}:
      Equal.trans(
        Maybe<&2, Types.Entry>,
        RKnown.Rev.seek(e2 <> r2, Nat.is_eq(1n+List.length(&2, Types.Entry, r2), k), e, 1n+List.length(&2, Types.Entry, r2), k),
        Snoc.pick(Nat.is_eq(1n+List.length(&2, Types.Entry, r2), k), e, List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), k)),
        List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, e2 <> r2), [e]), k),
        Lists.Bool.by(
          b => {
            RKnown.Rev.seek(e2 <> r2, b, e, 1n+List.length(&2, Types.Entry, r2), k)
              == Snoc.pick(b, e, List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), k)): Maybe<&2, Types.Entry>
          },
          Nat.is_eq(1n+List.length(&2, Types.Entry, r2), k),
          et => {==},
          ef => Rev.seek_eq(r2, e2, k)
        ),
        Equal.sym(
          Maybe<&2, Types.Entry>,
          List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, e2 <> r2), [e]), k),
          Snoc.pick(Nat.is_eq(1n+List.length(&2, Types.Entry, r2), k), e, List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), k)),
          (
            %Equal.sym(List<&2, Types.Entry>, List.reverse(&2, Types.Entry, e2 <> r2), List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), Rev.cons(e2, r2)): {List.get(&2, Types.Entry, List.append(&2, Types.Entry, _, [e]), k) == Snoc.pick(Nat.is_eq(1n+List.length(&2, Types.Entry, r2), k), e, List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), k)): Maybe<&2, Types.Entry>}
            %Equal.trans(Nat, List.length(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2])), 1n+List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r2)), 1n+List.length(&2, Types.Entry, r2), Shared.List.length_snoc(Types.Entry, List.reverse(&2, Types.Entry, r2), e2), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r2)), List.length(&2, Types.Entry, r2), Rev.length(r2))): {List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), [e]), k) == Snoc.pick(Nat.is_eq(_, k), e, List.get(&2, Types.Entry, List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), k)): Maybe<&2, Types.Entry>}
            Snoc.get(List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r2), [e2]), e, k))
        )
      )

# version k among versions, the newest first, with their count, is item k of
# the versions, the oldest first
def Rev.get_eq(rev: List<&2, Types.Entry>, +k: Nat) -> {
  RKnown.Rev.get(rev, List.length(&2, Types.Entry, rev), k)
    == List.get(&2, Types.Entry, List.reverse(&2, Types.Entry, rev), k): Maybe<&2, Types.Entry>
}:
  match rev:
    case Nil{}:
      {==}
    case Con{head, tail}:
      +head = head
      +tail = tail
      %Equal.sym(List<&2, Types.Entry>, List.reverse(&2, Types.Entry, head <> tail), List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, tail), [head]), Rev.cons(head, tail)) :
        {RKnown.Rev.seek(tail, Cmp.is_eq(Nat.cmp(List.length(&2, Types.Entry, tail), k)), head, List.length(&2, Types.Entry, tail), k) == List.get(&2, Types.Entry, _, k) : Maybe<&2, Types.Entry>}
      Rev.seek_eq(tail, head, k)

# the state that a node keeps of a state is that state
def Seen.of_state(st: RLines.State) -> {RKnown.Seen.state(RKnown.Seen.of(st)) == st: RLines.State}:
  match st:
    case RLines.State{+vs, +k}:
      Equal.cong(
        List<&2, Types.Entry>,
        RLines.State,
        z => RLines.State{z, k},
        List.reverse(&2, Types.Entry, List.reverse(&2, Types.Entry, vs)),
        vs,
        Rev.twice(vs)
      )

# what a node keeps of a state has the count of its versions
def Seen.of_counted(st: RLines.State) -> {
  RContents.Seen.counted(Some{RKnown.Seen.of(st)}) == True{}: Bool
}:
  match st:
    case RLines.State{versions, slot}:
      +versions = versions
      %Rev.length(versions) :
        {Cmp.is_eq(Nat.cmp(_, List.length(&2, Types.Entry, List.reverse.go(&2, Types.Entry, versions, [])))) == True{} : Bool}
      Shared.Nat.is_eq_refl(List.length(&2, Types.Entry, List.reverse.go(&2, Types.Entry, versions, [])))


# Reads of what the node keeps
# ----------------------------

# Seen.safe is Known.safe of the states that a node keeps
def Seen.safe_eq(
  c: Ledgers.Line,
  m: Maybe<&2, RKnown.Seen>,
  ms: Maybe<&2, RKnown.Seen>,
  k: Nat
) -> {
  RKnown.Seen.safe(c, m, ms, k)
    == RKnown.Known.safe(c, RKnown.Seen.state.of(m), RKnown.Seen.state.of(ms), k): Bool
}:
  match c m ms:
    case Ledgers.Line{h, None{}} m ms:
      {==}
    case Ledgers.Line{h, Some{b}} None{} ms:
      {==}
    case Ledgers.Line{h, Some{b}} Some{RKnown.Seen{rev, n, j}} None{}:
      {==}
    case Ledgers.Line{h, Some{b}} Some{RKnown.Seen{rev, n, j}} Some{y}:
      {==}

# Known.sound is Known.safe of the states that the table holds
def Known.sound_eq(+kn: RKnown.Known(), +c: Ledgers.Line, k: Nat) -> {
  RKnown.Known.sound(kn, c, k)
    == RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k): Bool
}:
  Seen.safe_eq(c, RKnown.Known.seen(kn, c), RKnown.Known.seen(kn, RKnown.Known.root(c)), k)

# Vote.waits.by, of what the table keeps of the line, is Slot.waits of its
# state
def Vote.waits_by(
  m: Maybe<&2, RKnown.Seen>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  m == RKnown.Known.seen(kn, c): Maybe<&2, RKnown.Seen>
} -> {
  RKnown.Vote.waits.by(m, kn, s, c, k) == RKnown.Slot.waits(RKnown.Known.state(kn, s, c), k): Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{RKnown.Seen{rev, n, j}}:
      e =>
        %e: {Nat.is_le(j, k) == RKnown.Slot.waits(RKnown.Known.state.of(RKnown.Seen.state.of(_), kn, s, c), k): Bool}
        {==}

# a ballot waits, as read from what the table keeps, when Slot.waits says so
# of the state of its line
def Vote.waits_eq(+kn: RKnown.Known(), +s: RFacts.Plain(), +c: Ledgers.Line, +k: Nat) -> {
  RKnown.Vote.waits(kn, s, c, k) == RKnown.Slot.waits(RKnown.Known.state(kn, s, c), k): Bool
}:
  Vote.waits_by(RKnown.Known.seen(kn, c), kn, s, c, k)({==})

# Line.waits.by, of what the table holds of the line, is Id.waits of its
# state
def Line.waits_by(
  j: RKnown.Info,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  j == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  RKnown.Line.waits.by(j, kn, s, c, i) == RKnown.Id.waits(RKnown.Known.state(kn, s, c), kn, c, i): Bool
}:
  match j:
    case RKnown.Info{c2, None{}, r, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, r, None{}}:
      e => {==}
    case RKnown.Info{c2, Some{RKnown.Seen{rev, n, k}}, r, Some{x}}:
      +e =>
        %e: {Bool.not(RKnown.Ids.has(x, i)) == RKnown.Id.waits(RKnown.Known.state.of(RKnown.Info.state(_), kn, s, c), kn, c, i): Bool}
        %e: {Bool.not(RKnown.Ids.has(x, i)) == Bool.not(RKnown.Made.in(RKnown.Info.ids(_), List.reverse(&2, Types.Entry, rev), i)): Bool}
        {==}

# a request waits on a line, as read from what the table holds, when
# Id.waits says so of the state of the line
def Line.waits_eq(+kn: RKnown.Known(), +s: RFacts.Plain(), +c: Ledgers.Line, +i: Ledgers.Id) -> {
  RKnown.Line.waits(kn, s, c, i) == RKnown.Id.waits(RKnown.Known.state(kn, s, c), kn, c, i): Bool
}:
  Line.waits_by(RKnown.Known.info(kn, c), kn, s, c, i)({==})

# Known.at.by, of what the table keeps of the line with the right count, is
# the version among the versions of the line
def Known.at_by(
  m: Maybe<&2, RKnown.Seen>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  m == RKnown.Known.seen(kn, c): Maybe<&2, RKnown.Seen>
} -> {
  RContents.Seen.counted(m) == True{}: Bool
} -> {
  RKnown.Known.at.by(m, kn, s, c, k)
    == RLines.Line.at.of(RKnown.Known.versions(kn, s, c), k): Maybe<&2, Types.Entry>
}:
  match m:
    case None{}:
      e => hc => {==}
    case Some{RKnown.Seen{+rev, +n, j}}:
      e => hc =>
        %e: {RKnown.Rev.get(rev, n, k) == RLines.Line.at.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, RKnown.Known.state.of(RKnown.Seen.state.of(_), kn, s, c)), k): Maybe<&2, Types.Entry>}
        %Equal.sym(Nat, n, List.length(&2, Types.Entry, rev), Shared.Nat.is_eq_sound(n, List.length(&2, Types.Entry, rev))(hc)): {RKnown.Rev.get(rev, _, k) == List.get(&2, Types.Entry, List.reverse(&2, Types.Entry, rev), k): Maybe<&2, Types.Entry>}
        Rev.get_eq(rev, k)

# a version of a line, as read from what the table keeps with the right
# count, is the version among the versions of the line
def Known.at_eq(+kn: RKnown.Known(), +s: RFacts.Plain(), +c: Ledgers.Line, +k: Nat) -> {
  RContents.Seen.counted(RKnown.Known.seen(kn, c)) == True{}: Bool
} -> {
  RKnown.Known.at(kn, s, c, k)
    == RLines.Line.at.of(RKnown.Known.versions(kn, s, c), k): Maybe<&2, Types.Entry>
}:
  hc => Known.at_by(RKnown.Known.seen(kn, c), kn, s, c, k)({==})(hc)

# Era.now.by, of what the table keeps of a store with the right count, is
# the newest of the versions of the store
def Era.now_by(
  m: Maybe<&2, RKnown.Seen>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash
) -> {
  m == RKnown.Known.seen(kn, Ledgers.Line{h, None{}}): Maybe<&2, RKnown.Seen>
} -> {
  RContents.Seen.counted(m) == True{}: Bool
} -> {RWorks.Era.now.by(m, kn, s, h) == RWorks.Era.now.of(RKnown.Known.store(kn, s, h)): Nat}:
  match m:
    case None{}:
      e => hc => {==}
    case Some{RKnown.Seen{+rev, +n, j}}:
      e => hc =>
        %e: {Nat.sub(n, 1n) == RWorks.Era.now.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, RKnown.Known.state.of(RKnown.Seen.state.of(_), kn, s, Ledgers.Line{h, None{}}))): Nat}
        %Equal.sym(Nat, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, rev)), List.length(&2, Types.Entry, rev), Rev.length(rev)): {Nat.sub(n, 1n) == Nat.sub(_, 1n): Nat}
        %Shared.Nat.is_eq_sound(n, List.length(&2, Types.Entry, rev))(hc): {Nat.sub(n, 1n) == Nat.sub(_, 1n): Nat}
        {==}


# What a work reads of what the node keeps
# ----------------------------------------

# Merges read from the newest versions
# ------------------------------------

# a pick of nothing so far, or else y, is the pick that leaves y
def Takes.pick_or(+c: Ledgers.Line, +j: Nat, m: Maybe<&2, Spec.Point>, +y: Maybe<&2, RWorks.Took>) -> {
  Maybe.or(&2, RWorks.Took, RWorks.Takes.pick(c, j, m, None{}), y) == RWorks.Takes.pick(c, j, m, y): Maybe<&2, RWorks.Took>
}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Point{+t, +v}}:
      Lists.Bool.by(
        d => {
          Maybe.or(&2, RWorks.Took, Bool.pick(Maybe<&2, RWorks.Took>, d, Some{RWorks.Took{j, v}}, None{}), y)
            == Bool.pick(Maybe<&2, RWorks.Took>, d, Some{RWorks.Took{j, v}}, y): Maybe<&2, RWorks.Took>
        },
        Ledgers.Line.is_eq(t, c),
        et => {==},
        ef => {==}
      )

# the newest version that takes a version of c, among some versions and one
# more, is that one when it takes one, else the newest among the others
def Takes.last_snoc(xs: List<&2, Types.Entry>, +e: Types.Entry, +c: Ledgers.Line, +k: Nat, +f: Maybe<&2, RWorks.Took>) -> {
  RWorks.Takes.last(List.append(&2, Types.Entry, xs, [e]), c, k, f)
    == RWorks.Takes.pick(c, Nat.add(List.length(&2, Types.Entry, xs), k), RContents.Entry.takes(e), RWorks.Takes.last(xs, c, k, f)): Maybe<&2, RWorks.Took>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(
        Maybe<&2, RWorks.Took>,
        RWorks.Takes.last(List.append(&2, Types.Entry, r, [e]), c, 1n+k, RWorks.Takes.pick(c, k, RContents.Entry.takes(x), f)),
        RWorks.Takes.pick(c, Nat.add(List.length(&2, Types.Entry, r), 1n+k), RContents.Entry.takes(e), RWorks.Takes.last(r, c, 1n+k, RWorks.Takes.pick(c, k, RContents.Entry.takes(x), f))),
        RWorks.Takes.pick(c, 1n+Nat.add(List.length(&2, Types.Entry, r), k), RContents.Entry.takes(e), RWorks.Takes.last(r, c, 1n+k, RWorks.Takes.pick(c, k, RContents.Entry.takes(x), f))),
        Takes.last_snoc(r, e, c, 1n+k, RWorks.Takes.pick(c, k, RContents.Entry.takes(x), f)),
        Equal.cong(
          Nat,
          Maybe<&2, RWorks.Took>,
          z => RWorks.Takes.pick(c, z, RContents.Entry.takes(e), RWorks.Takes.last(r, c, 1n+k, RWorks.Takes.pick(c, k, RContents.Entry.takes(x), f))),
          Nat.add(List.length(&2, Types.Entry, r), 1n+k),
          1n+Nat.add(List.length(&2, Types.Entry, r), k),
          Shared.Nat.add_succ(List.length(&2, Types.Entry, r), k)
        )
      )

# a walk from the newest of the versions rev finds the newest version that
# takes a version of c, as the walk from the oldest does, after prev
def Takes.seek_last(rev: List<&2, Types.Entry>, +c: Ledgers.Line, prev: Maybe<&2, RWorks.Took>) -> {
  RWorks.Takes.seek(rev, c, List.length(&2, Types.Entry, rev), prev)
    == Maybe.or(&2, RWorks.Took, prev, RWorks.Takes.last(List.reverse(&2, Types.Entry, rev), c, 0n, None{})): Maybe<&2, RWorks.Took>
}:
  match rev prev:
    case Nil{} None{}:
      {==}
    case Nil{} Some{t}:
      {==}
    case Con{e, r} Some{t}:
      {==}
    case Con{+e, +r} None{}:
      Equal.trans(
        Maybe<&2, RWorks.Took>,
        RWorks.Takes.seek(r, c, List.length(&2, Types.Entry, r), RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), None{})),
        RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})),
        RWorks.Takes.last(List.reverse(&2, Types.Entry, e <> r), c, 0n, None{}),
        Equal.trans(
          Maybe<&2, RWorks.Took>,
          RWorks.Takes.seek(r, c, List.length(&2, Types.Entry, r), RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), None{})),
          Maybe.or(&2, RWorks.Took, RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), None{}), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})),
          RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})),
          Takes.seek_last(r, c, RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), None{})),
          Takes.pick_or(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{}))
        ),
        (
          %Equal.sym(List<&2, Types.Entry>, List.reverse(&2, Types.Entry, e <> r), List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r), [e]), Rev.cons(e, r)): {
            RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})) == RWorks.Takes.last(_, c, 0n, None{}): Maybe<&2, RWorks.Took>
          }
          %Equal.sym(Maybe<&2, RWorks.Took>, RWorks.Takes.last(List.append(&2, Types.Entry, List.reverse(&2, Types.Entry, r), [e]), c, 0n, None{}), RWorks.Takes.pick(c, Nat.add(List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r)), 0n), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})), Takes.last_snoc(List.reverse(&2, Types.Entry, r), e, c, 0n, None{})): {
            RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})) == _: Maybe<&2, RWorks.Took>
          }
          %Equal.sym(Nat, Nat.add(List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r)), 0n), List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r)), Shared.Nat.add_zero(List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r)))): {
            RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})) == RWorks.Takes.pick(c, _, RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})): Maybe<&2, RWorks.Took>
          }
          %Equal.sym(Nat, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, r)), List.length(&2, Types.Entry, r), Rev.length(r)): {
            RWorks.Takes.pick(c, List.length(&2, Types.Entry, r), RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})) == RWorks.Takes.pick(c, _, RContents.Entry.takes(e), RWorks.Takes.last(List.reverse(&2, Types.Entry, r), c, 0n, None{})): Maybe<&2, RWorks.Took>
          }
          {==})
      )

# the pins of a merge read from the newest versions of both lines, when the
# table holds the versions rf of the line f, are the pins read from all
def Pins.merge_seen.of(
  +m: Nat,
  +c: Ledgers.Line,
  +f: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  y: RKnown.Seen
) -> {RKnown.Known.seen(kn, f) == Some{y}: Maybe<&2, RKnown.Seen>} -> {
  RWorks.Pins.merge.seen(m, c, f, rev, kn, s, Some{y})
    == RWorks.Pins.merge(m, c, f, List.reverse(&2, Types.Entry, rev), RKnown.Known.versions(kn, s, f)): Types.Pins
}:
  match y:
    case RKnown.Seen{+rf, +nf, +kf}:
      ey =>
        %Equal.sym(Maybe<&2, RKnown.Seen>, RKnown.Known.seen(kn, f), Some{RKnown.Seen{rf, nf, kf}}, ey): {
          RWorks.Pins.merge.seen(m, c, f, rev, kn, s, Some{RKnown.Seen{rf, nf, kf}})
            == RWorks.Pins.merge(m, c, f, List.reverse(&2, Types.Entry, rev), Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, RKnown.Known.state.of(RKnown.Seen.state.of(_), kn, s, f))): Types.Pins
        }
        %Equal.sym(Nat, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, rf)), List.length(&2, Types.Entry, rf), Rev.length(rf)): {
          RWorks.Pins.merge.seen(m, c, f, rev, kn, s, Some{RKnown.Seen{rf, nf, kf}})
            == RWorks.Pins.merge.of(m, c, f, Nat.sub(_, 1n), RWorks.Takes.last(List.reverse(&2, Types.Entry, rf), c, 0n, None{}), RWorks.Takes.last(List.reverse(&2, Types.Entry, rev), f, 0n, None{})): Types.Pins
        }
        %Equal.sym(Maybe<&2, RWorks.Took>, RWorks.Takes.seek(rf, c, List.length(&2, Types.Entry, rf), None{}), Maybe.or(&2, RWorks.Took, None{}, RWorks.Takes.last(List.reverse(&2, Types.Entry, rf), c, 0n, None{})), Takes.seek_last(rf, c, None{})): {
          RWorks.Pins.merge.of(m, c, f, Nat.sub(List.length(&2, Types.Entry, rf), 1n), _, RWorks.Takes.seek(rev, f, List.length(&2, Types.Entry, rev), None{}))
            == RWorks.Pins.merge.of(m, c, f, Nat.sub(List.length(&2, Types.Entry, rf), 1n), RWorks.Takes.last(List.reverse(&2, Types.Entry, rf), c, 0n, None{}), RWorks.Takes.last(List.reverse(&2, Types.Entry, rev), f, 0n, None{})): Types.Pins
        }
        %Equal.sym(Maybe<&2, RWorks.Took>, RWorks.Takes.seek(rev, f, List.length(&2, Types.Entry, rev), None{}), Maybe.or(&2, RWorks.Took, None{}, RWorks.Takes.last(List.reverse(&2, Types.Entry, rev), f, 0n, None{})), Takes.seek_last(rev, f, None{})): {
          RWorks.Pins.merge.of(m, c, f, Nat.sub(List.length(&2, Types.Entry, rf), 1n), RWorks.Takes.last(List.reverse(&2, Types.Entry, rf), c, 0n, None{}), _)
            == RWorks.Pins.merge.of(m, c, f, Nat.sub(List.length(&2, Types.Entry, rf), 1n), RWorks.Takes.last(List.reverse(&2, Types.Entry, rf), c, 0n, None{}), RWorks.Takes.last(List.reverse(&2, Types.Entry, rev), f, 0n, None{})): Types.Pins
        }
        {==}

# the pins of a merge read through the table are the pins read from all
def Pins.merge_seen(+m: Nat, +c: Ledgers.Line, +f: Ledgers.Line, +rev: List<&2, Types.Entry>, +kn: RKnown.Known(), +s: RFacts.Plain()) -> {
  RWorks.Pins.merge.seen(m, c, f, rev, kn, s, RKnown.Known.seen(kn, f))
    == RWorks.Pins.merge(m, c, f, List.reverse(&2, Types.Entry, rev), RKnown.Known.versions(kn, s, f)): Types.Pins
}:
  Lists.Maybe.by(
    RKnown.Seen,
    x => {
      RWorks.Pins.merge.seen(m, c, f, rev, kn, s, x)
        == RWorks.Pins.merge(m, c, f, List.reverse(&2, Types.Entry, rev), RKnown.Known.versions(kn, s, f)): Types.Pins
    },
    RKnown.Known.seen(kn, f),
    en => {==},
    y => ey => Pins.merge_seen.of(m, c, f, rev, kn, s, y)(ey)
  )

# the pins that Pins.seen gives are those that Pins.for gives for the
# versions, the oldest first
def Pins.seen_eq(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +m: Nat,
  r: Spec.Request
) -> {
  RWorks.Pins.seen(kn, s, c, rev, m, r) == RWorks.Pins.for(kn, s, c, List.reverse(&2, Types.Entry, rev), m, r): Types.Pins
}:
  match r:
    case Spec.Request.Start{owners}:
      {==}
    case Spec.Request.Write{branch, path, words}:
      {==}
    case Spec.Request.Merge{+from, into}:
      Pins.merge_seen(m, c, from, rev, kn, s)
    case Spec.Request.Resolve{merge, path1, words1}:
      {==}
    case Spec.Request.Mark{branch1, name, version}:
      {==}
    case Spec.Request.Move{branch2, to, version1}:
      {==}
    case Spec.Request.Group{store, name1, members}:
      {==}
    case Spec.Request.Own{line, group}:
      {==}

# the next slot of a line whose state and rule the table holds is read from
# them
def Work.open_seen(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +c2: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +n: Nat,
  +k2: Nat,
  +era: Nat,
  +g: Maybe<&2, String>,
  +ns: List<&2, String>,
  +x: Maybe<&2, RKnown.Ids>
) -> {
  RKnown.Info{c2, Some{RKnown.Seen{rev, n, k2}}, Some{RKnown.Mark{era, RLines.Rule{g, ns}}}, x} == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  Shared.Maybe.when(RWorks.Open, List.contains(~String, ~String.eq, ns, name), u2 => Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}})
    == RWorks.Work.open(kn, s, name, c): Maybe<&2, RWorks.Open>
}:
  x1 => (%x1 : {Shared.Maybe.when(RWorks.Open, List.contains(String, String.eq, ns, name), u2 => Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}}) == RWorks.Work.open.at(name, RKnown.Known.state.of(RKnown.Seen.state.of(RKnown.Info.seen(_)), kn, s, c), RWorks.Work.rule.or(RKnown.Mark.rule(RKnown.Info.mark(_)), kn, s, c, RKnown.Known.state.of(RKnown.Seen.state.of(RKnown.Info.seen(_)), kn, s, c))) : Maybe<&2, RWorks.Open>}; {==})

# whether a request made a version of a line whose ids the table holds is
# read from them
def Known.made_seen(
  +kn: RKnown.Known(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  +c2: Ledgers.Line,
  +m: Maybe<&2, RKnown.Seen>,
  +r: Maybe<&2, RKnown.Mark>,
  +x: RKnown.Ids
) -> {
  RKnown.Info{c2, m, r, Some{x}} == RKnown.Known.info(kn, c): RKnown.Info
} -> {RKnown.Ids.has(x, i) == RKnown.Known.made(kn, c, vs, i): Bool}:
  x1 => (%x1 : {RKnown.Ids.has(x, i) == RKnown.Made.in(RKnown.Info.ids(_), vs, i) : Bool}; {==})


# the vote for an ask on a line, as read from what the table holds of the
# line, is the vote at the next slot of the line
def Work.offer_by(
  j: RKnown.Info,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask
) -> {
  j == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  RWorks.Work.offer.by(j, kn, s, name, c, a)
    == RWorks.Work.offer.at(kn, s, name, c, a, RWorks.Work.open(kn, s, name, c)): Maybe<&2, RWorks.Plan>
}:
  match j:
    case RKnown.Info{c2, None{}, r, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, None{}, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, Some{w}, None{}}:
      e => {==}
    case RKnown.Info{+c2, Some{RKnown.Seen{+rev, +n, +k2}}, Some{RKnown.Mark{+era, RLines.Rule{+g, +ns}}}, Some{+x}}:
      +e =>
        %Work.open_seen(kn, s, name, c, c2, rev, n, k2, era, g, ns, Some{x})(e): {RWorks.Work.offer.if(List.contains(~String, ~String.eq, ns, name), RKnown.Ids.has(x, RLines.Ask.id(a)), kn, s, name, c, a, rev, k2, ns) == RWorks.Work.offer.at(kn, s, name, c, a, _): Maybe<&2, RWorks.Plan>}
        Lists.Bool.by(
          b => {
            RWorks.Work.offer.if(b, RKnown.Ids.has(x, RLines.Ask.id(a)), kn, s, name, c, a, rev, k2, ns)
              == RWorks.Work.offer.at(kn, s, name, c, a, Shared.Maybe.when(RWorks.Open, b, u2 => Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}})): Maybe<&2, RWorks.Plan>
          },
          List.contains(~String, ~String.eq, ns, name),
          et => (
            %Known.made_seen(kn, c, List.reverse(&2, Types.Entry, rev), RLines.Ask.id(a), c2, Some{RKnown.Seen{rev, n, k2}}, Some{RKnown.Mark{era, RLines.Rule{g, ns}}}, x)(e): {RWorks.Work.offer.if(True{}, RKnown.Ids.has(x, RLines.Ask.id(a)), kn, s, name, c, a, rev, k2, ns) == Shared.Maybe.when(RWorks.Plan, Bool.not(_), u => RWorks.Plan.of(c, k2, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(kn, s, c, List.reverse(&2, Types.Entry, rev), RWorks.Era.now(kn, s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name)))): Maybe<&2, RWorks.Plan>}
            %Pins.seen_eq(kn, s, c, rev, RWorks.Era.now(kn, s, c), RLines.Ask.request(a)): {RWorks.Work.offer.if(True{}, RKnown.Ids.has(x, RLines.Ask.id(a)), kn, s, name, c, a, rev, k2, ns) == Shared.Maybe.when(RWorks.Plan, Bool.not(RKnown.Ids.has(x, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k2, RWorks.Work.offer.of(u2 => Types.Pick{a, _}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name)))): Maybe<&2, RWorks.Plan>}
            Lists.Bool.by(
              b => {
                RWorks.Work.offer.if(True{}, b, kn, s, name, c, a, rev, k2, ns)
                  == Shared.Maybe.when(RWorks.Plan, Bool.not(b), u => RWorks.Plan.of(c, k2, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.seen(kn, s, c, rev, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name)))): Maybe<&2, RWorks.Plan>
              },
              RKnown.Ids.has(x, RLines.Ask.id(a)),
              et2 => {==},
              ef2 => {==}
            )),
          ef => {==}
        )

# the vote at the slot of a ballot, as read from what the table holds of
# the line, is the vote at the next slot of the line
def Work.follow_by(
  j: RKnown.Info,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  j == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  RWorks.Work.follow.by(j, kn, s, name, c, k)
    == RWorks.Work.follow.at(kn, s, name, c, k, RWorks.Work.open(kn, s, name, c)): Maybe<&2, RWorks.Plan>
}:
  match j:
    case RKnown.Info{c2, None{}, r, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, None{}, x}:
      e => {==}
    case RKnown.Info{+c2, Some{RKnown.Seen{+rev, +n, +k2}}, Some{RKnown.Mark{+era, RLines.Rule{+g, +ns}}}, +x}:
      e =>
        %Work.open_seen(kn, s, name, c, c2, rev, n, k2, era, g, ns, x)(e): {RWorks.Work.follow.if(List.contains(~String, ~String.eq, ns, name), Nat.is_eq(k2, k), kn, s, name, c, k, ns) == RWorks.Work.follow.at(kn, s, name, c, k, _): Maybe<&2, RWorks.Plan>}
        Lists.Bool.by(
          b => {
            RWorks.Work.follow.if(b, Nat.is_eq(k2, k), kn, s, name, c, k, ns)
              == RWorks.Work.follow.at(kn, s, name, c, k, Shared.Maybe.when(RWorks.Open, b, u2 => Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}})): Maybe<&2, RWorks.Plan>
          },
          List.contains(~String, ~String.eq, ns, name),
          et => Lists.Bool.by(
            b => {
              RWorks.Work.follow.if(True{}, b, kn, s, name, c, k, ns)
                == Shared.Maybe.when(RWorks.Plan, b, u => RWorks.Plan.of(c, k, RRounds.Slot.follow(RWorks.Work.ballots(kn, s, c, k), ns, k, name))): Maybe<&2, RWorks.Plan>
            },
            Nat.is_eq(k2, k),
            et2 => {==},
            ef2 => {==}
          ),
          ef => {==}
        )

# no pass for a node that is not one of those that decide the slot
def Work.pass_none(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  k: Maybe<&2, Nat>,
  i: Maybe<&2, Ledgers.Id>,
  +k2: Nat,
  +ns: List<&2, String>,
  +x: RKnown.Ids
) -> {
  RWorks.Work.pass.if(False{}, RWorks.Pass.due(k, i, k2, x), kn, s, name, c, k2, ns)
    == RWorks.Work.pass.at(kn, s, name, c, k, i, None{}): Maybe<&2, RWorks.Plan>
}:
  match k i:
    case Some{k1} i:
      {==}
    case None{} Some{id}:
      {==}
    case None{} None{}:
      {==}

# the pass of a node that is one of those that decide the slot, as read
# from what the table holds of the line
def Work.pass_seen(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  k: Maybe<&2, Nat>,
  i: Maybe<&2, Ledgers.Id>,
  +c2: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +n: Nat,
  +k2: Nat,
  +era: Nat,
  +g: Maybe<&2, String>,
  +ns: List<&2, String>,
  +x: RKnown.Ids
) -> {
  RKnown.Info{c2, Some{RKnown.Seen{rev, n, k2}}, Some{RKnown.Mark{era, RLines.Rule{g, ns}}}, Some{x}} == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  RWorks.Work.pass.if(True{}, RWorks.Pass.due(k, i, k2, x), kn, s, name, c, k2, ns)
    == RWorks.Work.pass.at(kn, s, name, c, k, i, Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}}): Maybe<&2, RWorks.Plan>
}:
  match k i:
    case Some{+k1} i:
      e => Lists.Bool.by(
        b => {
          RWorks.Work.pass.if(True{}, b, kn, s, name, c, k2, ns)
            == Shared.Maybe.when(RWorks.Plan, b, u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name))): Maybe<&2, RWorks.Plan>
        },
        Nat.is_eq(k2, k1),
        et => {==},
        ef => {==}
      )
    case None{} Some{+id}:
      e =>
        %Known.made_seen(kn, c, List.reverse(&2, Types.Entry, rev), id, c2, Some{RKnown.Seen{rev, n, k2}}, Some{RKnown.Mark{era, RLines.Rule{g, ns}}}, x)(e): {RWorks.Work.pass.if(True{}, Bool.not(RKnown.Ids.has(x, id)), kn, s, name, c, k2, ns) == Shared.Maybe.when(RWorks.Plan, Bool.not(_), u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name))): Maybe<&2, RWorks.Plan>}
        Lists.Bool.by(
          b => {
            RWorks.Work.pass.if(True{}, Bool.not(b), kn, s, name, c, k2, ns)
              == Shared.Maybe.when(RWorks.Plan, Bool.not(b), u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(RWorks.Work.ballots(kn, s, c, k2), ns, k2, name))): Maybe<&2, RWorks.Plan>
          },
          RKnown.Ids.has(x, id),
          et => {==},
          ef => {==}
        )
    case None{} None{}:
      e => {==}

# the pass at the next slot of a line, as read from what the table holds of
# the line, is the pass at the next slot of the line
def Work.pass_by(
  j: RKnown.Info,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Maybe<&2, Nat>,
  +i: Maybe<&2, Ledgers.Id>
) -> {
  j == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  RWorks.Work.pass.by(j, kn, s, name, c, k, i)
    == RWorks.Work.pass.at(kn, s, name, c, k, i, RWorks.Work.open(kn, s, name, c)): Maybe<&2, RWorks.Plan>
}:
  match j:
    case RKnown.Info{c2, None{}, r, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, None{}, x}:
      e => {==}
    case RKnown.Info{c2, Some{y}, Some{w}, None{}}:
      e => {==}
    case RKnown.Info{+c2, Some{RKnown.Seen{+rev, +n, +k2}}, Some{RKnown.Mark{+era, RLines.Rule{+g, +ns}}}, Some{+x}}:
      +e =>
        %Work.open_seen(kn, s, name, c, c2, rev, n, k2, era, g, ns, Some{x})(e): {RWorks.Work.pass.if(List.contains(~String, ~String.eq, ns, name), RWorks.Pass.due(k, i, k2, x), kn, s, name, c, k2, ns) == RWorks.Work.pass.at(kn, s, name, c, k, i, _): Maybe<&2, RWorks.Plan>}
        Lists.Bool.by(
          b => {
            RWorks.Work.pass.if(b, RWorks.Pass.due(k, i, k2, x), kn, s, name, c, k2, ns)
              == RWorks.Work.pass.at(kn, s, name, c, k, i, Shared.Maybe.when(RWorks.Open, b, u2 => Some{RWorks.Open{List.reverse(&2, Types.Entry, rev), k2, ns}})): Maybe<&2, RWorks.Plan>
          },
          List.contains(~String, ~String.eq, ns, name),
          et => Work.pass_seen(kn, s, name, c, k, i, c2, rev, n, k2, era, g, ns, x)(e),
          ef => Work.pass_none(kn, s, name, c, k, i, k2, ns, x)
        )


# A run, as the node keeps it
# ---------------------------

# what the run q, as the node keeps it, leaves of a line
def Pace.run(q: RKnown.Pace) -> RKnown.Run:
  match q:
    case RKnown.Pace{x, m, u, ids}:
      RKnown.Run{RKnown.Seen.state(x), m, u, ids}

# what the run m, as the node keeps it, leaves of a line, if any
def Pace.run.of(m: Maybe<&2, RKnown.Pace>) -> Maybe<&2, RKnown.Run>:
  match m:
    case None{}:
      None{}
    case Some{q}:
      Some{Pace.run(q)}

# the state that the run q keeps
def Pace.seen(q: RKnown.Pace) -> RKnown.Seen:
  match q:
    case RKnown.Pace{x, m, u, ids}:
      x

# the rule that Pace.rule gives is the rule that Run.rule gives with the
# versions of the store, the oldest first
def Pace.rule_eq(
  same: Bool,
  rr: List<&2, Types.Entry>,
  c: Ledgers.Line,
  m: Nat,
  u: Maybe<&2, RLines.Rule>
) -> {
  RKnown.Pace.rule(same, rr, c, m, u)
    == RKnown.Run.rule(same, List.reverse(&2, Types.Entry, rr), c, m, u): Maybe<&2, RLines.Rule>
}:
  match same:
    case False{}:
      {==}
    case True{}:
      {==}

# what Pace.put leaves is what Run.put leaves
def Pace.put_eq(
  dup: Bool,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +n: Nat,
  +k: Nat,
  +m: Nat,
  +u: Maybe<&2, RLines.Rule>,
  +x: RKnown.Ids,
  +pk: Types.Pick
) -> {
  Pace.run(RKnown.Pace.put(dup, rr, c, rev, n, k, m, u, x, pk))
    == RKnown.Run.put(dup, List.reverse(&2, Types.Entry, rr), c, List.reverse(&2, Types.Entry, rev), k, m, u, x, pk): RKnown.Run
}:
  match dup:
    case True{}:
      {==}
    case False{}:
      %Rev.cons(Types.Entry{pk, k}, rev): {Pace.run(RKnown.Pace.put(False{}, rr, c, rev, n, k, m, u, x, pk)) == RKnown.Run{RLines.State{_, 1n+k}, Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), RKnown.Run.rule(Nat.is_eq(Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), m), List.reverse(&2, Types.Entry, rr), c, Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), u), RKnown.Ids.put(x, Types.Entry{pk, k})}: RKnown.Run}
      %Pace.rule_eq(Nat.is_eq(Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), m), rr, c, Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), u): {Pace.run(RKnown.Pace.put(False{}, rr, c, rev, n, k, m, u, x, pk)) == RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, Types.Entry{pk, k} <> rev), 1n+k}, Nat.max(RLines.Entry.era(Types.Entry{pk, k}), m), _, RKnown.Ids.put(x, Types.Entry{pk, k})}: RKnown.Run}
      {==}

# what Pace.step.of leaves is what Run.step.of leaves
def Pace.step_of_eq(
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  q: RKnown.Pace,
  p: Maybe<&2, Types.Pick>
) -> {
  Pace.run.of(RKnown.Pace.step.of(rr, c, q, p))
    == RKnown.Run.step.of(List.reverse(&2, Types.Entry, rr), c, Pace.run(q), p): Maybe<&2, RKnown.Run>
}:
  match q p:
    case RKnown.Pace{RKnown.Seen{rev, n, k}, m, u, x} None{}:
      {==}
    case RKnown.Pace{RKnown.Seen{+rev, +n, +k}, +m, +u, +x} Some{+pk}:
      Equal.cong(
        RKnown.Run,
        Maybe<&2, RKnown.Run>,
        z => Some{z},
        Pace.run(RKnown.Pace.put(RKnown.Ids.has(x, RLines.Pick.id(pk)), rr, c, rev, n, k, m, u, x, pk)),
        RKnown.Run.put(RKnown.Ids.has(x, RLines.Pick.id(pk)), List.reverse(&2, Types.Entry, rr), c, List.reverse(&2, Types.Entry, rev), k, m, u, x, pk),
        Pace.put_eq(RKnown.Ids.has(x, RLines.Pick.id(pk)), rr, c, rev, n, k, m, u, x, pk)
      )

# what Pace.step leaves is what Run.step leaves
def Pace.step_eq(
  +fs: List<&2, Types.Fact>,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  q: RKnown.Pace
) -> {
  Pace.run.of(RKnown.Pace.step(fs, rr, c, q))
    == RKnown.Run.step(fs, List.reverse(&2, Types.Entry, rr), c, Pace.run(q)): Maybe<&2, RKnown.Run>
}:
  match q:
    case RKnown.Pace{seen, era, rule, ids}:
      match seen:
        case RKnown.Seen{rev, count, slot}:
          match rule:
            case None{}:
              {==}
            case Some{value}:
              +slot = slot
              +value = value
              %Equal.sym(Maybe<&2, RKnown.Run>, Pace.run.of(RKnown.Pace.step.of(rr, c, RKnown.Pace{RKnown.Seen{rev, count, slot}, era, Some{value}, ids}, RRounds.Rounds.won(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), [RRounds.Lead.mind.at(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.pick(RRounds.Ballot, RRounds.Roll, RRounds.Ballot.counts, RRounds.Slot.ballots(fs, c, slot), RRounds.Roll{RRounds.Slot.ballots(fs, c, slot), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))}))]), RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), 0n))), RKnown.Run.step.of(List.reverse(&2, Types.Entry, rr), c, Pace.run(RKnown.Pace{RKnown.Seen{rev, count, slot}, era, Some{value}, ids}), RRounds.Rounds.won(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), [RRounds.Lead.mind.at(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.pick(RRounds.Ballot, RRounds.Roll, RRounds.Ballot.counts, RRounds.Slot.ballots(fs, c, slot), RRounds.Roll{RRounds.Slot.ballots(fs, c, slot), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))}))]), RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), 0n)), Pace.step_of_eq(rr, c, RKnown.Pace{RKnown.Seen{rev, count, slot}, era, Some{value}, ids}, RRounds.Rounds.won(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), [RRounds.Lead.mind.at(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.pick(RRounds.Ballot, RRounds.Roll, RRounds.Ballot.counts, RRounds.Slot.ballots(fs, c, slot), RRounds.Roll{RRounds.Slot.ballots(fs, c, slot), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))}))]), RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), 0n))) :
                {_ == RKnown.Run.step.of(List.reverse.go(&2, Types.Entry, rr, []), c, RKnown.Run{RLines.State{List.reverse.go(&2, Types.Entry, rev, []), slot}, era, Some{value}, ids}, RRounds.Rounds.won(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), [RRounds.Lead.mind.at(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.pick(RRounds.Ballot, RRounds.Roll, RRounds.Ballot.counts, RRounds.Slot.ballots(fs, c, slot), RRounds.Roll{RRounds.Slot.ballots(fs, c, slot), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(slot, Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot)))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, slot))}))]), RRounds.Slot.ballots(fs, c, slot), RLines.Rule.nodes(value), 0n)) : Maybe<&2, RKnown.Run>}
              {==}

# what Pace.go leaves is what Run.go leaves
def Pace.go_eq(
  fuel: Nat,
  +fs: List<&2, Types.Fact>,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: RKnown.Pace,
  m: Maybe<&2, RKnown.Pace>
) -> {
  Pace.run(RKnown.Pace.go(fuel, fs, rr, c, q, m))
    == RKnown.Run.go(fuel, fs, List.reverse(&2, Types.Entry, rr), c, Pace.run(q), Pace.run.of(m)): RKnown.Run
}:
  match fuel m:
    case 0n m:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{+q2}:
      %Pace.step_eq(fs, rr, c, q2): {Pace.run(RKnown.Pace.go(f, fs, rr, c, q2, RKnown.Pace.step(fs, rr, c, q2))) == RKnown.Run.go(f, fs, List.reverse(&2, Types.Entry, rr), c, Pace.run(q2), _): RKnown.Run}
      Pace.go_eq(f, fs, rr, c, q2, RKnown.Pace.step(fs, rr, c, q2))

# what Pace.from leaves is what Run.from leaves
def Pace.from_eq(
  +fs: List<&2, Types.Fact>,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: RKnown.Pace
) -> {
  Pace.run(RKnown.Pace.from(fs, rr, c, q))
    == RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), c, Pace.run(q)): RKnown.Run
}:
  %Pace.step_eq(fs, rr, c, q) :
    {Pace.run(RKnown.Pace.go(1n+RLines.Line.bound(fs, c), fs, rr, c, q, RKnown.Pace.step.at(fs, rr, c, q, RKnown.Pace.nodes(q)))) == RKnown.Run.go(1n+RLines.Line.bound(fs, c), fs, List.reverse.go(&2, Types.Entry, rr, []), c, Pace.run(q), _) : RKnown.Run}
  Pace.go_eq(1n+RLines.Line.bound(fs, c), fs, rr, c, q, RKnown.Pace.step.at(fs, rr, c, q, RKnown.Pace.nodes(q)))


# One write of what the table holds of a line
# -------------------------------------------

# Binds.insert_lt, read from right to left
def Insert.lt_rev(
  -V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Orders.Key.lt(k, k1) == True{}: Bool
} -> {
  Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v): List<&2, Crits.Bind<V>>
}:
  hl => Equal.sym(
    List<&2, Crits.Bind<V>>,
    Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v),
    Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r,
    Orders.Binds.insert_lt(V, k1, v1, r, k, v)(hl)
  )

# Binds.insert_gt, read from right to left
def Insert.gt_rev(
  -V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Orders.Key.lt(k, k1) == False{}: Bool
} -> {
  Crits.Key.is_eq(k1, k) == False{}: Bool
} -> {
  Crits.Bind{k1, v1} <> Orders.Binds.insert(V, r, k, v) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v): List<&2, Crits.Bind<V>>
}:
  hl => he => Equal.sym(
    List<&2, Crits.Bind<V>>,
    Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v),
    Crits.Bind{k1, v1} <> Orders.Binds.insert(V, r, k, v),
    Orders.Binds.insert_gt(V, k1, v1, r, k, v)(hl)(he)
  )

# an insert of the first key puts its value in the first entry
def Insert.hit_rev(
  -V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Orders.Key.lt(k, k1) == False{}: Bool
} -> {
  Crits.Key.is_eq(k1, k) == True{}: Bool
} -> {
  Crits.Bind{k1, v} <> r == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v): List<&2, Crits.Bind<V>>
}:
  hl => he =>
    %Equal.sym(Bool, Orders.Key.lt(k, k1), False{}, hl): {Crits.Bind{k1, v} <> r == Shared.Bool.when(List<&2, Crits.Bind<V>>, _, u => Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r, u => Shared.Bool.when(List<&2, Crits.Bind<V>>, Crits.Key.is_eq(k1, k), w => Crits.Bind{k1, v} <> r, w => Crits.Bind{k1, v1} <> Orders.Binds.insert(V, r, k, v))): List<&2, Crits.Bind<V>>}
    %Equal.sym(Bool, Crits.Key.is_eq(k1, k), True{}, he): {Crits.Bind{k1, v} <> r == Shared.Bool.when(List<&2, Crits.Bind<V>>, _, w => Crits.Bind{k1, v} <> r, w => Crits.Bind{k1, v1} <> Orders.Binds.insert(V, r, k, v)): List<&2, Crits.Bind<V>>}
    {==}

# an insert of a key into sorted entries, and then an insert of the same
# key, is the second insert
def Binds.insert_twice(
  -V: Data,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +a: V,
  +b: V
) -> {
  Orders.Binds.insert(V, Orders.Binds.insert(V, es, k, a), k, b)
    == Orders.Binds.insert(V, es, k, b): List<&2, Crits.Bind<V>>
}:
  match es:
    case Nil{}:
      %Insert.hit_rev(V, k, a, [], k, b)(Crits.Bits.lt_self(Crits.Key.bits(k)))(Crits.Key.is_eq_refl(k)): {_ == [Crits.Bind{k, b}]: List<&2, Crits.Bind<V>>}
      {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      Lists.Bool.by(
        bl => {Orders.Binds.insert(V, Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, a), k, b) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>},
        Orders.Key.lt(k, k1),
        +et => (
          %Insert.lt_rev(V, k1, v1, r, k, a)(et): {Orders.Binds.insert(V, _, k, b) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
          %Insert.hit_rev(V, k, a, Crits.Bind{k1, v1} <> r, k, b)(Crits.Bits.lt_self(Crits.Key.bits(k)))(Crits.Key.is_eq_refl(k)): {_ == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
          Insert.lt_rev(V, k1, v1, r, k, b)(et)),
        +ef => Lists.Bool.by(
          be => {Orders.Binds.insert(V, Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, a), k, b) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>},
          Crits.Key.is_eq(k1, k),
          +et2 => (
            %Insert.hit_rev(V, k1, v1, r, k, a)(ef)(et2): {Orders.Binds.insert(V, _, k, b) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
            %Insert.hit_rev(V, k1, a, r, k, b)(ef)(et2): {_ == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
            Insert.hit_rev(V, k1, v1, r, k, b)(ef)(et2)),
          +ef2 => (
            %Insert.gt_rev(V, k1, v1, r, k, a)(ef)(ef2): {Orders.Binds.insert(V, _, k, b) == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
            %Insert.gt_rev(V, k1, v1, Orders.Binds.insert(V, r, k, a), k, b)(ef)(ef2): {_ == Orders.Binds.insert(V, Crits.Bind{k1, v1} <> r, k, b): List<&2, Crits.Bind<V>>}
            %Insert.gt_rev(V, k1, v1, r, k, b)(ef)(ef2): {Crits.Bind{k1, v1} <> Orders.Binds.insert(V, Orders.Binds.insert(V, r, k, a), k, b) == _: List<&2, Crits.Bind<V>>}
            %Binds.insert_twice(V, r, k, a, b): {Crits.Bind{k1, v1} <> Orders.Binds.insert(V, Orders.Binds.insert(V, r, k, a), k, b) == Crits.Bind{k1, v1} <> _: List<&2, Crits.Bind<V>>}
            {==})
        )
      )

# a write of a key into a well formed map, and then a write of the same
# key, is the second write
def Crit.set_twice(
  ~V: Data,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>,
  +a: V,
  +b: V
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crits.Crit.set(~V, m, k, b) == Crits.Crit.set(~V, Crits.Crit.set(~V, m, k, a), k, b): Crits.Crit<V>
}:
  +h => Crits.Crit.ext(
    ~V,
    Crits.Crit.set(~V, m, k, b),
    Crits.Crit.set(~V, Crits.Crit.set(~V, m, k, a), k, b)
  )(
    Crits.Crit.upsert_wf(~V, ~(w => x => x), m, k, b)(h)
  )(
    Crits.Crit.upsert_wf(~V, ~(w => x => x), Crits.Crit.set(~V, m, k, a), k, b)(Crits.Crit.upsert_wf(~V, ~(w => x => x), m, k, a)(h))
  )(
    Equal.trans(
      List<&2, Crits.Bind<V>>,
      Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, b)),
      Orders.Binds.insert(V, Crits.Crit.entries(V, m), k, b),
      Crits.Crit.entries(V, Crits.Crit.set(~V, Crits.Crit.set(~V, m, k, a), k, b)),
      Orders.Crit.entries_set(~V, m, k, b)(h),
      Equal.sym(
        List<&2, Crits.Bind<V>>,
        Crits.Crit.entries(V, Crits.Crit.set(~V, Crits.Crit.set(~V, m, k, a), k, b)),
        Orders.Binds.insert(V, Crits.Crit.entries(V, m), k, b),
        Equal.trans(
          List<&2, Crits.Bind<V>>,
          Crits.Crit.entries(V, Crits.Crit.set(~V, Crits.Crit.set(~V, m, k, a), k, b)),
          Orders.Binds.insert(V, Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, a)), k, b),
          Orders.Binds.insert(V, Crits.Crit.entries(V, m), k, b),
          Orders.Crit.entries_set(~V, Crits.Crit.set(~V, m, k, a), k, b)(Crits.Crit.upsert_wf(~V, ~(w => x => x), m, k, a)(h)),
          (
            %Equal.sym(List<&2, Crits.Bind<V>>, Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, a)), Orders.Binds.insert(V, Crits.Crit.entries(V, m), k, a), Orders.Crit.entries_set(~V, m, k, a)(h)): {Orders.Binds.insert(V, _, k, b) == Orders.Binds.insert(V, Crits.Crit.entries(V, m), k, b): List<&2, Crits.Bind<V>>}
            Binds.insert_twice(V, Crits.Crit.entries(V, m), k, a, b))
        )
      )
    )
  )

# what well formed lines hold of a line after a write of it is what was
# written
def Infos.with_of(
  +l: Crits.Crit<RKnown.Info>,
  +c: Ledgers.Line,
  +m: Maybe<&2, RKnown.Seen>,
  +r: Maybe<&2, RKnown.Mark>,
  +x: Maybe<&2, RKnown.Ids>
) -> {
  Crits.Crit.wf(~RKnown.Info, l, 0n) == True{}: Bool
} -> {
  RKnown.Info{c, m, r, x} == RKnown.Infos.of(RKnown.Infos.with(l, RKnown.Info{c, m, r, x}), c): RKnown.Info
}:
  x1 => (%Equal.sym(Maybe<&2, RKnown.Info>, Crits.Crit.get(RKnown.Info, Crits.Crit.set(RKnown.Info, l, Ledgers.Line.code(c, []), RKnown.Info{c, m, r, x}), Ledgers.Line.code(c, [])), Bool.pick(Maybe<&2, RKnown.Info>, Crits.Key.is_eq(Ledgers.Line.code(c, []), Ledgers.Line.code(c, [])), Some{RKnown.Info{c, m, r, x}}, Crits.Crit.get(RKnown.Info, l, Ledgers.Line.code(c, []))), Crits.Dict.get_set.at(~RKnown.Info, l, Ledgers.Line.code(c, []), RKnown.Info{c, m, r, x}, Ledgers.Line.code(c, []))(x1)) : {RKnown.Info{c, m, r, x} == RKnown.Info.or(_, c) : RKnown.Info}; (%Equal.sym(Bool, Crits.Key.is_eq(Ledgers.Line.code(c, []), Ledgers.Line.code(c, [])), True{}, Crits.Key.is_eq_refl(Ledgers.Line.code(c, []))) : {RKnown.Info{c, m, r, x} == RKnown.Info.or(Bool.pick(Maybe<&2, RKnown.Info>, _, Some{RKnown.Info{c, m, r, x}}, Crits.Crit.get(RKnown.Info, l, Ledgers.Line.code(c, []))), c) : RKnown.Info}; {==}))

# a write of a line into well formed lines, and then a write of the same
# line, is the second write
def Infos.with_twice(
  +l: Crits.Crit<RKnown.Info>,
  +c: Ledgers.Line,
  +i: RKnown.Info,
  +i2: RKnown.Info
) -> {
  Crits.Crit.wf(~RKnown.Info, l, 0n) == True{}: Bool
} -> {
  RKnown.Info.key(i) == RKnown.Info.key(i2): List<&2, U32>
} -> {
  RKnown.Infos.with(l, i2) == RKnown.Infos.with(RKnown.Infos.with(l, i), i2): Crits.Crit<RKnown.Info>
}:
  x => x1 => (%x1 : {Crits.Crit.set(~RKnown.Info, l, _, i2) == Crits.Crit.set(~RKnown.Info, Crits.Crit.set(~RKnown.Info, l, RKnown.Info.key(i), i), _, i2) : Crits.Crit<RKnown.Info>}; Crit.set_twice(~RKnown.Info, l, Ledgers.Line.code(RKnown.Info.line(i), []), i, i2)(x))

# what a node keeps of the state that it keeps, with the right count, is
# what it keeps
def Seen.state_of(+rev: List<&2, Types.Entry>, +n: Nat, +k: Nat) -> {
  Nat.is_eq(n, List.length(&2, Types.Entry, rev)) == True{}: Bool
} -> {
  RKnown.Seen{rev, n, k} == RKnown.Seen.of(RKnown.Seen.state(RKnown.Seen{rev, n, k})): RKnown.Seen
}:
  hc =>
    %Equal.sym(List<&2, Types.Entry>, List.reverse(&2, Types.Entry, List.reverse(&2, Types.Entry, rev)), rev, Rev.twice(rev)): {RKnown.Seen{rev, n, k} == RKnown.Seen{_, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, rev)), k}: RKnown.Seen}
    %Equal.sym(Nat, List.length(&2, Types.Entry, List.reverse(&2, Types.Entry, rev)), List.length(&2, Types.Entry, rev), Rev.length(rev)): {RKnown.Seen{rev, n, k} == RKnown.Seen{rev, _, k}: RKnown.Seen}
    %Shared.Nat.is_eq_sound(n, List.length(&2, Types.Entry, rev))(hc): {RKnown.Seen{rev, n, k} == RKnown.Seen{rev, _, k}: RKnown.Seen}
    {==}

# a table that holds nothing of a line, with a state of the line, holds the
# state
def Known.add_kept(
  +l: Crits.Crit<RKnown.Info>,
  +hs: Crits.Crit<RKnown.Held>,
  +q: Nat,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Crits.Crit.wf(~RKnown.Info, l, 0n) == True{}: Bool
} -> {
  RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{RKnown.Seen.of(st)}, None{}, None{}}), None{}, hs, q}
    == RKnown.Known.add(RKnown.Kept{c, st}, RKnown.Table{RKnown.Infos.with(l, RKnown.Info.blank(c)), None{}, hs, q}): RKnown.Known()
}:
  +h =>
    %Infos.with_of(l, c, None{}, None{}, None{})(h): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{RKnown.Seen.of(st)}, None{}, None{}}), None{}, hs, q} == RKnown.Table{RKnown.Infos.with(RKnown.Infos.with(l, RKnown.Info.blank(c)), RKnown.Info.state.set(_, st)), None{}, hs, q}: RKnown.Known()}
    %Infos.with_twice(l, c, RKnown.Info.blank(c), RKnown.Info{c, Some{RKnown.Seen.of(st)}, None{}, None{}})(h)({==}): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{RKnown.Seen.of(st)}, None{}, None{}}), None{}, hs, q} == RKnown.Table{_, None{}, hs, q}: RKnown.Known()}
    {==}

# a table that holds a state of a line, with the ids of its versions, holds
# both
def Known.add_made(
  +l: Crits.Crit<RKnown.Info>,
  +hs: Crits.Crit<RKnown.Held>,
  +q: Nat,
  +c: Ledgers.Line,
  +y: RKnown.Seen,
  +ids: RKnown.Ids
) -> {
  Crits.Crit.wf(~RKnown.Info, l, 0n) == True{}: Bool
} -> {
  RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, Some{ids}}), None{}, hs, q}
    == RKnown.Known.add(RKnown.Made{c, ids}, RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, None{}}), None{}, hs, q}): RKnown.Known()
}:
  +h =>
    %Infos.with_of(l, c, Some{y}, None{}, None{})(h): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, Some{ids}}), None{}, hs, q} == RKnown.Table{RKnown.Infos.with(RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, None{}}), RKnown.Info.ids.set(_, ids)), None{}, hs, q}: RKnown.Known()}
    %Infos.with_twice(l, c, RKnown.Info{c, Some{y}, None{}, None{}}, RKnown.Info{c, Some{y}, None{}, Some{ids}})(h)({==}): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, Some{ids}}), None{}, hs, q} == RKnown.Table{_, None{}, hs, q}: RKnown.Known()}
    {==}

# a table that holds a state and the ids of a line, with the era and the
# rule of its next version, if any, holds the three
def Known.rule_put(
  +l: Crits.Crit<RKnown.Info>,
  +hs: Crits.Crit<RKnown.Held>,
  +q: Nat,
  +c: Ledgers.Line,
  +y: RKnown.Seen,
  +ids: RKnown.Ids,
  +m: Nat,
  u: Maybe<&2, RLines.Rule>
) -> {
  Crits.Crit.wf(~RKnown.Info, l, 0n) == True{}: Bool
} -> {
  RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, RKnown.Mark.of(m, u), Some{ids}}), None{}, hs, q}
    == RKnown.Known.rule.put(RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, Some{ids}}), None{}, hs, q}, c, m, u): RKnown.Known()
}:
  match u:
    case None{}:
      h => {==}
    case Some{+rule}:
      +h =>
        %Infos.with_of(l, c, Some{y}, None{}, Some{ids})(h): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, Some{RKnown.Mark{m, rule}}, Some{ids}}), None{}, hs, q} == RKnown.Table{RKnown.Infos.with(RKnown.Infos.with(l, RKnown.Info{c, Some{y}, None{}, Some{ids}}), RKnown.Info.mark.set(_, m, rule)), None{}, hs, q}: RKnown.Known()}
        %Infos.with_twice(l, c, RKnown.Info{c, Some{y}, None{}, Some{ids}}, RKnown.Info{c, Some{y}, Some{RKnown.Mark{m, rule}}, Some{ids}})(h)({==}): {RKnown.Table{RKnown.Infos.with(l, RKnown.Info{c, Some{y}, Some{RKnown.Mark{m, rule}}, Some{ids}}), None{}, hs, q} == RKnown.Table{_, None{}, hs, q}: RKnown.Known()}
        {==}

# the table that Known.paced gives is the table that Known.ran gives after
# a ballot that leaves the other lines as they are
def Known.paced_eq(
  +kn: RKnown.Known(),
  +h: Hashes.Hash,
  +b: String,
  q: RKnown.Pace
) -> {
  Crits.Crit.wf(~RKnown.Info, RKnown.Known.lines(kn), 0n) == True{}: Bool
} -> {
  RContents.Seen.counted(Some{Pace.seen(q)}) == True{}: Bool
} -> {
  RKnown.Known.paced(kn, Ledgers.Line{h, Some{b}}, q)
    == RKnown.Known.ran(
      RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))),
      Ledgers.Line{h, Some{b}},
      Pace.run(q)
    ): RKnown.Known()
}:
  match q:
    case RKnown.Pace{RKnown.Seen{+rev, +n, +k}, +m, +u, +ids}:
      +hw => hc =>
        %Known.add_kept(RKnown.Known.lines(kn), RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn), Ledgers.Line{h, Some{b}}, RLines.State{List.reverse(&2, Types.Entry, rev), k})(hw): {RKnown.Table{RKnown.Infos.with(RKnown.Known.lines(kn), RKnown.Info{Ledgers.Line{h, Some{b}}, Some{RKnown.Seen{rev, n, k}}, RKnown.Mark.of(m, u), Some{ids}}), None{}, RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn)} == RKnown.Known.rule.put(RKnown.Known.add(RKnown.Made{Ledgers.Line{h, Some{b}}, ids}, _), Ledgers.Line{h, Some{b}}, m, u): RKnown.Known()}
        %Seen.state_of(rev, n, k)(hc): {RKnown.Table{RKnown.Infos.with(RKnown.Known.lines(kn), RKnown.Info{Ledgers.Line{h, Some{b}}, Some{RKnown.Seen{rev, n, k}}, RKnown.Mark.of(m, u), Some{ids}}), None{}, RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn)} == RKnown.Known.rule.put(RKnown.Known.add(RKnown.Made{Ledgers.Line{h, Some{b}}, ids}, RKnown.Table{RKnown.Infos.with(RKnown.Known.lines(kn), RKnown.Info{Ledgers.Line{h, Some{b}}, Some{_}, None{}, None{}}), None{}, RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn)}), Ledgers.Line{h, Some{b}}, m, u): RKnown.Known()}
        %Known.add_made(RKnown.Known.lines(kn), RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn), Ledgers.Line{h, Some{b}}, RKnown.Seen{rev, n, k}, ids)(hw): {RKnown.Table{RKnown.Infos.with(RKnown.Known.lines(kn), RKnown.Info{Ledgers.Line{h, Some{b}}, Some{RKnown.Seen{rev, n, k}}, RKnown.Mark.of(m, u), Some{ids}}), None{}, RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn)} == RKnown.Known.rule.put(_, Ledgers.Line{h, Some{b}}, m, u): RKnown.Known()}
        Known.rule_put(RKnown.Known.lines(kn), RKnown.Known.stock(kn), 1n+RKnown.Known.low(kn), Ledgers.Line{h, Some{b}}, RKnown.Seen{rev, n, k}, ids, m, u)(hw)


# a run that puts a version keeps the count of the versions right
def Pace.put_counted(
  dup: Bool,
  rr: List<&2, Types.Entry>,
  c: Ledgers.Line,
  rev: List<&2, Types.Entry>,
  n: Nat,
  k: Nat,
  m: Nat,
  u: Maybe<&2, RLines.Rule>,
  x: RKnown.Ids,
  pk: Types.Pick
) -> {
  Nat.is_eq(n, List.length(&2, Types.Entry, rev)) == True{}: Bool
} -> {
  RContents.Seen.counted(Some{Pace.seen(RKnown.Pace.put(dup, rr, c, rev, n, k, m, u, x, pk))}) == True{}: Bool
}:
  match dup:
    case False{}:
      x1 => x1
    case True{}:
      x1 => x1

# the count of the versions of the run m, if any, is right
def Pace.counted(m: Maybe<&2, RKnown.Pace>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{q}:
      RContents.Seen.counted(Some{Pace.seen(q)})

# a step of a run keeps the count of the versions right
def Pace.step_of_counted(
  rr: List<&2, Types.Entry>,
  c: Ledgers.Line,
  q: RKnown.Pace,
  p: Maybe<&2, Types.Pick>
) -> {
  RContents.Seen.counted(Some{Pace.seen(q)}) == True{}: Bool
} -> {Pace.counted(RKnown.Pace.step.of(rr, c, q, p)) == True{}: Bool}:
  match q p:
    case RKnown.Pace{RKnown.Seen{rev, n, k}, m, u, x} None{}:
      hc => {==}
    case RKnown.Pace{RKnown.Seen{rev, n, k}, m, u, +x} Some{+pk}:
      hc => Pace.put_counted(RKnown.Ids.has(x, RLines.Pick.id(pk)), rr, c, rev, n, k, m, u, x, pk)(hc)

# a step of a run, read from facts, keeps the count of the versions right
def Pace.step_counted(
  fs: List<&2, Types.Fact>,
  rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: RKnown.Pace
) -> {
  RContents.Seen.counted(Some{Pace.seen(q)}) == True{}: Bool
} -> {Pace.counted(RKnown.Pace.step(fs, rr, c, q)) == True{}: Bool}:
  match q:
    case RKnown.Pace{seen, era, rule, ids}:
      match rule:
        case None{}:
          x => {==}
        case Some{value}:
          +fs = fs
          x => Pace.step_of_counted(rr, c, RKnown.Pace{seen, era, Some{value}, ids}, RRounds.Rounds.won(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RLines.Rule.nodes(value), RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})))), [RRounds.Lead.mind.at(RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RLines.Rule.nodes(value), RRounds.Rounds.minds(RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RLines.Rule.nodes(value), RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}))), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}))))), Lists.List.pick(RRounds.Ballot, RRounds.Roll, RRounds.Ballot.counts, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RRounds.Roll{RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RRounds.Turn.of(RLines.Rule.nodes(value), Nat.add(RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids}))))), Lists.List.peak(RRounds.Ballot, RRounds.Ballot.round, RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})))}))]), RRounds.Slot.ballots(fs, c, RKnown.Pace.slot(RKnown.Pace{seen, era, Some{value}, ids})), RLines.Rule.nodes(value), 0n))(x)

# a run keeps the count of the versions right
def Pace.go_counted(
  fuel: Nat,
  +fs: List<&2, Types.Fact>,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  q: RKnown.Pace,
  m: Maybe<&2, RKnown.Pace>
) -> {
  RContents.Seen.counted(Some{Pace.seen(q)}) == True{}: Bool
} -> {
  Pace.counted(m) == True{}: Bool
} -> {
  RContents.Seen.counted(Some{Pace.seen(RKnown.Pace.go(fuel, fs, rr, c, q, m))}) == True{}: Bool
}:
  match fuel m:
    case 0n m:
      hq => hm => hq
    case 1n+f None{}:
      hq => hm => hq
    case 1n+f Some{+q2}:
      hq => +hm => Pace.go_counted(f, fs, rr, c, q2, RKnown.Pace.step(fs, rr, c, q2))(hm)(Pace.step_counted(fs, rr, c, q2)(hm))

# a run from a state with the right count leaves the right count
def Pace.from_counted(
  +fs: List<&2, Types.Fact>,
  +rr: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: RKnown.Pace
) -> {
  RContents.Seen.counted(Some{Pace.seen(q)}) == True{}: Bool
} -> {
  RContents.Seen.counted(Some{Pace.seen(RKnown.Pace.from(fs, rr, c, q))}) == True{}: Bool
}:
  +hq => Pace.go_counted(
    1n+RLines.Line.bound(fs, c),
    fs,
    rr,
    c,
    q,
    RKnown.Pace.step(fs, rr, c, q)
  )(hq)(Pace.step_counted(fs, rr, c, q)(hq))

# The table after a ballot
# ------------------------

# the table that Known.cast.as gives, when the table holds all that the run
# of a branch reads and the ballot is for its next slot: what the run
# leaves, in the table without what the ballot may change
def Quick.all(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +fs: List<&2, Types.Fact>,
  +c2: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  +n: Nat,
  +slot: Nat,
  +era: Nat,
  +rule: RLines.Rule,
  +ids: RKnown.Ids,
  +rr: List<&2, Types.Entry>,
  +rn: Nat,
  +rk: Nat
) -> {
  RKnown.Info{c2, Some{RKnown.Seen{rev, n, slot}}, Some{RKnown.Mark{era, rule}}, Some{ids}} == RKnown.Known.info(kn, Ledgers.Line{h, Some{b}}): RKnown.Info
} -> {
  Some{RKnown.Seen{rr, rn, rk}} == RKnown.Known.seen(kn, Ledgers.Line{h, None{}}): Maybe<&2, RKnown.Seen>
} -> {
  True{} == Nat.is_eq(slot, k): Bool
} -> {
  RKnown.Known.ran(
    RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))),
    Ledgers.Line{h, Some{b}},
    RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})
  )
    == RKnown.Known.cast.as(RKnown.Known.quick(kn, Ledgers.Line{h, Some{b}}, k, Some{fs}), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}): RKnown.Known()
}:
  +e1 => +e2 => +e3 =>
    %e1: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.cast.as(RKnown.Known.quick.of(Some{fs}, Ledgers.Line{h, Some{b}}, k, RKnown.Info.state(_), RKnown.Known.find(kn, Ledgers.Line{h, None{}}), RKnown.Mark.era(RKnown.Info.mark(_)), RKnown.Mark.rule(RKnown.Info.mark(_)), RKnown.Info.ids(_)), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}): RKnown.Known()}
    %e2: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.cast.as(RKnown.Known.quick.of(Some{fs}, Ledgers.Line{h, Some{b}}, k, Some{RLines.State{List.reverse(&2, Types.Entry, rev), slot}}, RKnown.Seen.state.of(_), Some{era}, Some{rule}, Some{ids}), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}): RKnown.Known()}
    %e3: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.cast.as(Shared.Maybe.when(RKnown.Run, _, z => Some{RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})}), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}): RKnown.Known()}
    %e1: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.spared(RKnown.Known.safe(Ledgers.Line{h, Some{b}}, RKnown.Info.state(_), RKnown.Known.find(kn, Ledgers.Line{h, None{}}), k), kn)), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})): RKnown.Known()}
    %e2: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.spared(RKnown.Known.safe(Ledgers.Line{h, Some{b}}, Some{RLines.State{List.reverse(&2, Types.Entry, rev), slot}}, RKnown.Seen.state.of(_), k), kn)), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})): RKnown.Known()}
    %e3: {RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})) == RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.spared(_, kn)), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})): RKnown.Known()}
    {==}

# Known.cast.by, of what the table holds of a line and of its store, with
# the right count, is Known.cast.as of the run that Known.quick gives
def Known.cast_by(
  +w: Maybe<&2, List<&2, Types.Fact>>,
  +c: Ledgers.Line,
  j: RKnown.Info,
  ms: Maybe<&2, RKnown.Seen>,
  +k: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  j == RKnown.Known.info(kn, c): RKnown.Info
} -> {
  ms == RKnown.Known.seen(kn, RKnown.Known.root(c)): Maybe<&2, RKnown.Seen>
} -> {
  Crits.Crit.wf(~RKnown.Info, RKnown.Known.lines(kn), 0n) == True{}: Bool
} -> {
  RContents.Seen.counted(RKnown.Info.seen(j)) == True{}: Bool
} -> {
  RKnown.Known.cast.by(w, c, j, ms, k, kn, s)
    == RKnown.Known.cast.as(RKnown.Known.quick(kn, c, k, w), kn, s, c, k, w): RKnown.Known()
}:
  match w c j ms:
    case None{} c j ms:
      e1 => e2 => hw => hc => {==}
    case Some{fs} Ledgers.Line{h, None{}} j ms:
      e1 => e2 => hw => hc => {==}
    case Some{fs} Ledgers.Line{h, Some{b}} RKnown.Info{c2, None{}, r, x} ms:
      e1 => e2 => hw => hc => {==}
    case Some{fs} Ledgers.Line{h, Some{b}} RKnown.Info{c2, Some{RKnown.Seen{rev, n, slot}}, None{}, x} ms:
      e1 => e2 => hw => hc => {==}
    case Some{fs} Ledgers.Line{h, Some{b}} RKnown.Info{c2, Some{RKnown.Seen{rev, n, slot}}, Some{RKnown.Mark{era, rule}}, None{}} ms:
      e1 => e2 => hw => hc => {==}
    case Some{fs} Ledgers.Line{h, Some{b}} RKnown.Info{c2, Some{RKnown.Seen{rev, n, slot}}, Some{RKnown.Mark{era, rule}}, Some{ids}} None{}:
      e1 => e2 => hw => hc => {==}
    case Some{+fs} Ledgers.Line{+h, Some{+b}} RKnown.Info{+c2, Some{RKnown.Seen{+rev, +n, +slot}}, Some{RKnown.Mark{+era, +rule}}, Some{+ids}} Some{RKnown.Seen{+rr, +rn, +rk}}:
      e1 => e2 => hw => hc => Lists.Bool.by(
        bn => {
          RKnown.Known.cast.if(bn, fs, Ledgers.Line{h, Some{b}}, RKnown.Seen{rev, n, slot}, RKnown.Seen{rr, rn, rk}, era, rule, ids, k, kn, s)
            == RKnown.Known.cast.as(RKnown.Known.quick(kn, Ledgers.Line{h, Some{b}}, k, Some{fs}), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}): RKnown.Known()
        },
        Nat.is_eq(slot, k),
        et => Equal.trans(
          RKnown.Known(),
          RKnown.Known.paced(kn, Ledgers.Line{h, Some{b}}, RKnown.Pace.from(fs, rr, Ledgers.Line{h, Some{b}}, RKnown.Pace{RKnown.Seen{rev, n, slot}, era, Some{rule}, ids})),
          RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, RKnown.Run.from(fs, List.reverse(&2, Types.Entry, rr), Ledgers.Line{h, Some{b}}, RKnown.Run{RLines.State{List.reverse(&2, Types.Entry, rev), slot}, era, Some{rule}, ids})),
          RKnown.Known.cast.as(RKnown.Known.quick(kn, Ledgers.Line{h, Some{b}}, k, Some{fs}), kn, s, Ledgers.Line{h, Some{b}}, k, Some{fs}),
          (
            %Pace.from_eq(fs, rr, Ledgers.Line{h, Some{b}}, RKnown.Pace{RKnown.Seen{rev, n, slot}, era, Some{rule}, ids}): {RKnown.Known.paced(kn, Ledgers.Line{h, Some{b}}, RKnown.Pace.from(fs, rr, Ledgers.Line{h, Some{b}}, RKnown.Pace{RKnown.Seen{rev, n, slot}, era, Some{rule}, ids})) == RKnown.Known.ran(RKnown.Known.join(RKnown.Known.voted(kn, Ledgers.Line{h, Some{b}}), RKnown.Known.deeper(RKnown.Known.contents(kn))), Ledgers.Line{h, Some{b}}, _): RKnown.Known()}
            Known.paced_eq(kn, h, b, RKnown.Pace.from(fs, rr, Ledgers.Line{h, Some{b}}, RKnown.Pace{RKnown.Seen{rev, n, slot}, era, Some{rule}, ids}))(hw)(Pace.from_counted(fs, rr, Ledgers.Line{h, Some{b}}, RKnown.Pace{RKnown.Seen{rev, n, slot}, era, Some{rule}, ids})(hc))),
          Quick.all(kn, s, h, b, k, fs, c2, rev, n, slot, era, rule, ids, rr, rn, rk)(e1)(e2)(Equal.sym(Bool, Nat.is_eq(slot, k), True{}, et))
        ),
        ef => {==}
      )

# the table after a ballot, as read from what a well formed table holds
# with the right count, is the table that Known.cast.as gives of the run
# that Known.quick gives
def Known.cast_eq(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> {
  Crits.Crit.wf(~RKnown.Info, RKnown.Known.lines(kn), 0n) == True{}: Bool
} -> {
  RContents.Seen.counted(RKnown.Known.seen(kn, c)) == True{}: Bool
} -> {
  RKnown.Known.cast(kn, s, c, k, w)
    == RKnown.Known.cast.as(RKnown.Known.quick(kn, c, k, w), kn, s, c, k, w): RKnown.Known()
}:
  hw => hc => Known.cast_by(w, c, RKnown.Known.info(kn, c), RKnown.Known.seen(kn, RKnown.Known.root(c)), k, kn, s)({==})({==})(hw)(hc)

# What an answer reads of what the node keeps
# -------------------------------------------

# the status that Status.by.seen gives is the status that Status.by gives
# for the versions, the oldest first
def Status.by_seen(
  +rev: List<&2, Types.Entry>,
  +k: Nat,
  +i: Ledgers.Id,
  r: Spec.Request,
  +cs: Maybe<&2, List<&2, String>>
) -> {
  RAnswers.Status.by.seen(rev, k, i, r, cs)
    == RAnswers.Status.by(List.reverse(&2, Types.Entry, rev), k, i, r, cs): Spec.Status
}:
  match r:
    case Spec.Request.Start{owners}:
      {==}
    case Spec.Request.Write{branch, path, words}:
      {==}
    case Spec.Request.Merge{from, into}:
      {==}
    case Spec.Request.Resolve{merge, path1, words1}:
      {==}
    case Spec.Request.Mark{branch1, name, version}:
      {==}
    case Spec.Request.Move{branch2, to, version1}:
      {==}
    case Spec.Request.Group{store, name1, members}:
      {==}
    case Spec.Request.Own{line, group}:
      {==}

# the reply that Reply.status.seen gives is the reply that Reply.status
# gives for the versions, the oldest first
def Reply.status_seen(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +rev: List<&2, Types.Entry>,
  m: Maybe<&2, RKnown.Found>
) -> {
  RAnswers.Reply.status.seen(kn, s, c, rev, m)
    == RAnswers.Reply.status(kn, s, c, Some{List.reverse(&2, Types.Entry, rev)}, m): Maybe<&2, Spec.Reply>
}:
  match m:
    case None{}:
      {==}
    case Some{value}:
      match value:
        case RKnown.Found{n, entry}:
          +n = n
          +entry = entry
          %Status.by_seen(rev, n, RLines.Ask.id(RLines.Entry.ask(entry)), RLines.Ask.request(RLines.Entry.ask(entry)), RAnswers.Clashes.of(kn, s, c, n, entry)) :
            {Some{Spec.Reply.Status{RAnswers.Status.by.seen(rev, n, RLines.Ask.id(RLines.Entry.ask(entry)), RLines.Ask.request(RLines.Entry.ask(entry)), RAnswers.Clashes.of(kn, s, c, n, entry))}} == Some{Spec.Reply.Status{_}} : Maybe<&2, Spec.Reply>}
          {==}

# Reply.status.by, of what the table keeps of the line, is Reply.status of
# the versions of the line
def Reply.status_by(
  x: Maybe<&2, RKnown.Seen>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +m: Maybe<&2, RKnown.Found>
) -> {
  x == RKnown.Known.seen(kn, c): Maybe<&2, RKnown.Seen>
} -> {
  RAnswers.Reply.status.by(x, kn, s, c, m)
    == RAnswers.Reply.status(kn, s, c, RKnown.Known.versions(kn, s, c), m): Maybe<&2, Spec.Reply>
}:
  match x:
    case None{}:
      e => {==}
    case Some{RKnown.Seen{+rev, n, j}}:
      e =>
        %e: {RAnswers.Reply.status.seen(kn, s, c, rev, m) == RAnswers.Reply.status(kn, s, c, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, RKnown.Known.state.of(RKnown.Seen.state.of(_), kn, s, c)), m): Maybe<&2, Spec.Reply>}
        Reply.status_seen(kn, s, c, rev, m)

# a number less itself is zero
def Nat.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      Nat.sub_self(ap)

# Merge.hint.seen is Merge.hint of the state that a node keeps
def Merge.hint_seen(m: Maybe<&2, RKnown.Seen>, t: Spec.Point, a: Spec.Point) -> {
  RContents.Merge.hint.seen(m, t, a)
    == RContents.Merge.hint(RKnown.Seen.state.of(m), t, a): Maybe<&2, List<&2, RContents.Write>>
}:
  match m t a:
    case None{} t a:
      {==}
    case Some{RKnown.Seen{+rev, n, k}} Spec.Point{+tl, +tn} Spec.Point{+al, +an}:
      Lists.Bool.by(
        b => {
          RContents.Merge.hint.if(b, RKnown.Seen{rev, n, k}, tl, tn, al, an)
            == RContents.Merge.hint(Some{RLines.State{List.reverse(&2, Types.Entry, rev), k}}, Spec.Point{tl, tn}, Spec.Point{al, an}): Maybe<&2, List<&2, RContents.Write>>
        },
        Nat.is_eq(tn, an),
        et => (
          %Equal.sym(Nat, tn, an, Shared.Nat.is_eq_sound(tn, an)(et)): {Shared.Maybe.when(List<&2, RContents.Write>, Ledgers.Line.is_eq(al, tl), u => Some{[]}) == Shared.Maybe.when(List<&2, RContents.Write>, List.all.if(u => Nat.is_le(an, _), Ledgers.Line.is_eq(al, tl)), u => RContents.Writes.of(Nat.sub(_, an), List.drop(&2, Types.Entry, List.reverse(&2, Types.Entry, rev), 1n+an))): Maybe<&2, List<&2, RContents.Write>>}
          %Equal.sym(Nat, Nat.sub(an, an), 0n, Nat.sub_self(an)): {Shared.Maybe.when(List<&2, RContents.Write>, Ledgers.Line.is_eq(al, tl), u => Some{[]}) == Shared.Maybe.when(List<&2, RContents.Write>, List.all.if(u => Nat.is_le(an, an), Ledgers.Line.is_eq(al, tl)), u => RContents.Writes.of(_, List.drop(&2, Types.Entry, List.reverse(&2, Types.Entry, rev), 1n+an))): Maybe<&2, List<&2, RContents.Write>>}
          %Equal.sym(Bool, Nat.is_le(an, an), True{}, Shared.Nat.le_refl(an)): {Shared.Maybe.when(List<&2, RContents.Write>, Ledgers.Line.is_eq(al, tl), u => Some{[]}) == Shared.Maybe.when(List<&2, RContents.Write>, List.all.if(u => _, Ledgers.Line.is_eq(al, tl)), u => Some{[]}): Maybe<&2, List<&2, RContents.Write>>}
          Lists.Bool.by(
            b2 => {
              Shared.Maybe.when(List<&2, RContents.Write>, b2, u => Some{[]})
                == Shared.Maybe.when(List<&2, RContents.Write>, List.all.if(u => True{}, b2), u => Some{[]}): Maybe<&2, List<&2, RContents.Write>>
            },
            Ledgers.Line.is_eq(al, tl),
            et2 => {==},
            ef2 => {==}
          )),
        ef => {==}
      )

# the next slot of a state, read from the facts of a node as a list, is the
# one read from the facts, once the rule u of the slot is known
def Step.at_in_eq(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +st: RLines.State,
  u: Maybe<&2, RLines.Rule>
) -> {
  RLines.Line.step.at(
    s,
    c,
    st,
    u
  )
    == RLines.Line.step.at.in(RFacts.Facts.list(s), c, st, u): Maybe<&2, RLines.State>
}:
  match u:
    case None{}:
      {==}
    case Some{rule}:
      {==}

# the next slot of a state, read from the facts of a node as a list, is the
# one read from the facts
def Step.in_eq(
  +s: RFacts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  RLines.Line.step(
    s,
    r,
    c,
    st
  )
    == RLines.Line.step.in(RFacts.Facts.list(s), r, c, st): Maybe<&2, RLines.State>
}:
  Step.at_in_eq(s, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))

# a run that reads the facts of a node as a list is the run that reads the
# facts
def Run.in_eq(
  f: Nat,
  +s: RFacts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State,
  m: Maybe<&2, RLines.State>
) -> {
  RLines.Line.run(
    f,
    s,
    r,
    c,
    st,
    m
  )
    == RLines.Line.run.in(f, RFacts.Facts.list(s), r, c, st, m): RLines.State
}:
  match f m:
    case 0n None{}:
      {==}
    case 0n Some{st2}:
      {==}
    case 1n+p None{}:
      {==}
    case 1n+p Some{+st2}:
      (
        %Step.in_eq(s, r, c, st2): {RLines.Line.run(p, s, r, c, st2, RLines.Line.step(s, r, c, st2)) == RLines.Line.run.in(p, RFacts.Facts.list(s), r, c, st2, _): RLines.State}
        Run.in_eq(p, s, r, c, st2, RLines.Line.step(s, r, c, st2)))


# A run read from the votes of its line
# -------------------------------------

# the ballots of a slot of a line are those among the votes of the line
def Ballots.votes(fs: List<&2, Types.Fact>, +c: Ledgers.Line, +k: Nat) -> {
  RRounds.Slot.ballots(RLines.Line.votes(fs, c), c, k) == RRounds.Slot.ballots(fs, c, k): List<&2, RRounds.Ballot>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{a}, rest}:
      Ballots.votes(rest, c, k)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      Ballots.votes(rest, c, k)
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t}, +x}, +rest}:
      Lists.Bool.by(
        d => {
          RRounds.Slot.ballots(List.filter.put(Types.Fact, Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x}, RLines.Line.votes(rest, c), d), c, k)
            == List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(rest, c, k), Bool.and(d, Nat.is_eq(k2, k))): List<&2, RRounds.Ballot>
        },
        Ledgers.Line.is_eq(c2, c),
        et => (
          %Equal.sym(Bool, Ledgers.Line.is_eq(c2, c), True{}, et): {
            List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(RLines.Line.votes(rest, c), c, k), Bool.and(_, Nat.is_eq(k2, k)))
              == List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(rest, c, k), Nat.is_eq(k2, k)): List<&2, RRounds.Ballot>
          }
          Equal.cong(
            List<&2, RRounds.Ballot>,
            List<&2, RRounds.Ballot>,
            z => List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, z, Nat.is_eq(k2, k)),
            RRounds.Slot.ballots(RLines.Line.votes(rest, c), c, k),
            RRounds.Slot.ballots(rest, c, k),
            Ballots.votes(rest, c, k)
          )),
        ef => Ballots.votes(rest, c, k)
      )

# the bound of a line is the bound of its votes
def Bound.votes(fs: List<&2, Types.Fact>, +c: Ledgers.Line) -> {
  RLines.Line.bound(RLines.Line.votes(fs, c), c) == RLines.Line.bound(fs, c): Nat
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{a}, rest}:
      Bound.votes(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      Bound.votes(rest, c)
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t}, +x}, +rest}:
      Lists.Bool.by(
        d => {
          RLines.Line.bound(List.filter.put(Types.Fact, Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x}, RLines.Line.votes(rest, c), d), c)
            == Nat.max(RLines.Line.bound.at(d, k2), RLines.Line.bound(rest, c)): Nat
        },
        Ledgers.Line.is_eq(c2, c),
        et => (
          %Equal.sym(Bool, Ledgers.Line.is_eq(c2, c), True{}, et): {
            Nat.max(RLines.Line.bound.at(_, k2), RLines.Line.bound(RLines.Line.votes(rest, c), c))
              == Nat.max(1n+k2, RLines.Line.bound(rest, c)): Nat
          }
          Equal.cong(
            Nat,
            Nat,
            z => Nat.max(1n+k2, z),
            RLines.Line.bound(RLines.Line.votes(rest, c), c),
            RLines.Line.bound(rest, c),
            Bound.votes(rest, c)
          )),
        ef => Bound.votes(rest, c)
      )

# a step of a line read from its votes, once the rule u of the slot is
# known, is the step read from all the facts
def Step.at_votes(+fs: List<&2, Types.Fact>, +c: Ledgers.Line, +st: RLines.State, u: Maybe<&2, RLines.Rule>) -> {
  RLines.Line.step.at.in(RLines.Line.votes(fs, c), c, st, u) == RLines.Line.step.at.in(fs, c, st, u): Maybe<&2, RLines.State>
}:
  match u:
    case None{}:
      {==}
    case Some{+rule}:
      Equal.cong(
        List<&2, RRounds.Ballot>,
        Maybe<&2, RLines.State>,
        z => RLines.Line.step.of(st, RRounds.Slot.decided(z, RLines.Rule.nodes(rule), RLines.State.slot(st))),
        RRounds.Slot.ballots(RLines.Line.votes(fs, c), c, RLines.State.slot(st)),
        RRounds.Slot.ballots(fs, c, RLines.State.slot(st)),
        Ballots.votes(fs, c, RLines.State.slot(st))
      )

# a step of a line read from its votes is the step read from all the facts
def Step.votes(+fs: List<&2, Types.Fact>, +r: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +st: RLines.State) -> {
  RLines.Line.step.in(RLines.Line.votes(fs, c), r, c, st) == RLines.Line.step.in(fs, r, c, st): Maybe<&2, RLines.State>
}:
  Step.at_votes(fs, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))

# a run of a line read from its votes is the run read from all the facts
def Run.votes(f: Nat, +fs: List<&2, Types.Fact>, +r: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +st: RLines.State, m: Maybe<&2, RLines.State>) -> {
  RLines.Line.run.in(f, RLines.Line.votes(fs, c), r, c, st, m) == RLines.Line.run.in(f, fs, r, c, st, m): RLines.State
}:
  match f m:
    case 0n m:
      {==}
    case 1n+p None{}:
      {==}
    case 1n+p Some{+st2}:
      %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.step.in(RLines.Line.votes(fs, c), r, c, st2), RLines.Line.step.in(fs, r, c, st2), Step.votes(fs, r, c, st2)): {
        RLines.Line.run.in(p, RLines.Line.votes(fs, c), r, c, st2, _) == RLines.Line.run.in(p, fs, r, c, st2, RLines.Line.step.in(fs, r, c, st2)): RLines.State
      }
      Run.votes(p, fs, r, c, st2, RLines.Line.step.in(fs, r, c, st2))

# a run of a line from st, read from its votes, is the run from st
def Start.in_eq(+s: RFacts.Plain(), +r: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +st: RLines.State) -> {
  RLines.Line.start.in(RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st) == RLines.Line.start(s, r, c, st): RLines.State
}:
  %Equal.sym(Nat, RLines.Line.bound(RLines.Line.votes(RFacts.Facts.list(s), c), c), RLines.Line.bound(RFacts.Facts.list(s), c), Bound.votes(RFacts.Facts.list(s), c)): {
    RLines.Line.run.in(_, RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st, RLines.Line.step.in(RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st)) == RLines.Line.start(s, r, c, st): RLines.State
  }
  %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.step.in(RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st), RLines.Line.step.in(RFacts.Facts.list(s), r, c, st), Step.votes(RFacts.Facts.list(s), r, c, st)): {
    RLines.Line.run.in(RLines.Line.bound(RFacts.Facts.list(s), c), RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st, _) == RLines.Line.start(s, r, c, st): RLines.State
  }
  %Step.in_eq(s, r, c, st): {
    RLines.Line.run.in(RLines.Line.bound(RFacts.Facts.list(s), c), RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st, _) == RLines.Line.start(s, r, c, st): RLines.State
  }
  Equal.trans(
    RLines.State,
    RLines.Line.run.in(RLines.Line.bound(RFacts.Facts.list(s), c), RLines.Line.votes(RFacts.Facts.list(s), c), r, c, st, RLines.Line.step(s, r, c, st)),
    RLines.Line.run.in(RLines.Line.bound(RFacts.Facts.list(s), c), RFacts.Facts.list(s), r, c, st, RLines.Line.step(s, r, c, st)),
    RLines.Line.start(s, r, c, st),
    Run.votes(RLines.Line.bound(RFacts.Facts.list(s), c), RFacts.Facts.list(s), r, c, st, RLines.Line.step(s, r, c, st)),
    Equal.sym(
      RLines.State,
      RLines.Line.start(s, r, c, st),
      RLines.Line.run.in(RLines.Line.bound(RFacts.Facts.list(s), c), RFacts.Facts.list(s), r, c, st, RLines.Line.step(s, r, c, st)),
      Run.in_eq(RLines.Line.bound(RFacts.Facts.list(s), c), s, r, c, st, RLines.Line.step(s, r, c, st))
    )
  )

# the state of a branch read from its votes is its state
def Branch.state_in(+s: RFacts.Plain(), +c: Ledgers.Line, +rr: List<&2, Types.Entry>) -> {
  RLines.Branch.state.in(RFacts.Facts.list(s), c, rr) == RLines.Branch.state(s, c, Some{rr}): Maybe<&2, RLines.State>
}:
  Lists.Maybe.by(
    Types.Entry,
    m => {
      RLines.Branch.state.of(RLines.Line.votes(RFacts.Facts.list(s), c), c, rr, m) == RLines.Line.from(s, Some{rr}, c, m): Maybe<&2, RLines.State>
    },
    RLines.Branch.first(rr, c),
    en => {==},
    e => ee => Equal.cong(
      RLines.State,
      Maybe<&2, RLines.State>,
      z => Some{z},
      RLines.Line.start.in(RLines.Line.votes(RFacts.Facts.list(s), c), Some{rr}, c, RLines.State{[e], 1n}),
      RLines.Line.start(s, Some{rr}, c, RLines.State{[e], 1n}),
      Start.in_eq(s, Some{rr}, c, RLines.State{[e], 1n})
    )
  )
