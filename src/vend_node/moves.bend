import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types


# What one more fact does
# -----------------------
# What the lines read after a node takes in an ask, or casts a vote. No law
# here needs the facts to name no liar.

# what a node adds to its facts: an ask that it takes in, or a vote that it
# casts for a slot of a line
type Delta is Data:
  Delta.Ask{name: String, ask: Types.Ask}
  Delta.Vote{name: String, line: Ledgers.Line, slot: Nat, pick: Types.Pick}

# the facts s after the node adds d
def Delta.to(d: Delta, +s: Facts.Facts()) -> Facts.Facts():
  match d:
    case Delta.Ask{name, a}:
      Facts.Facts.take(name, s, Types.Fact.Ask{a})
    case Delta.Vote{name, c, k, pk}:
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk})

# the facts s after the node adds d (f), or before
def Delta.side(d: Delta, +s: Facts.Facts(), f: Bool) -> Facts.Facts():
  match f:
    case True{}:
      Delta.to(d, s)
    case False{}:
      s

# d starts no store
def Delta.ok(d: Delta) -> Bool:
  match d:
    case Delta.Ask{name, a}:
      Bool.not(Facts.Request.is_start(Lines.Ask.request(a)))
    case Delta.Vote{name, c, k, pk}:
      True{}

# d is no vote for the slot j of the line c2
def Delta.keeps(d: Delta, c2: Ledgers.Line, j: Nat) -> Bool:
  match d:
    case Delta.Ask{name, a}:
      True{}
    case Delta.Vote{name, c, k, pk}:
      Bool.not(Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)))

# d is no vote for a slot of the line c2
def Delta.spares(d: Delta, c2: Ledgers.Line) -> Bool:
  match d:
    case Delta.Ask{name, a}:
      True{}
    case Delta.Vote{name, c, k, pk}:
      Bool.not(Ledgers.Line.is_eq(c2, c))

# the fact f is a vote for the slot j of the line c2
def Fact.is_at(f: Types.Fact, c2: Ledgers.Line, j: Nat) -> Bool:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{c, k}, pk}:
      Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k))
    case _:
      False{}

# the fact f is an ask
def Fact.is_ask(f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{a}:
      True{}
    case Types.Fact.Vote{v, st, pk}:
      False{}

# the pick of the fact f, if it is a vote
def Fact.pick(f: Types.Fact) -> Maybe<&2, Types.Pick>:
  match f:
    case Types.Fact.Ask{a}:
      None{}
    case Types.Fact.Vote{v, st, pk}:
      Some{pk}

# a vote for another slot is another fact
def Fact.vote_ne(
  +v: String,
  +c2: Ledgers.Line,
  +j: Nat,
  +q: Types.Pick,
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick
) -> {Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)) == False{}: Bool} -> {
  Coded.Fact.is_eq(Types.Fact.Vote{v, Types.Step.At{c2, j}, q}, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}) == False{}: Bool
}:
  +ne => Lists.Bool.by(
    b => {b == False{}: Bool},
    Coded.Fact.is_eq(Types.Fact.Vote{v, Types.Step.At{c2, j}, q}, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}),
    et => Lists.Bool.clash(
      {True{} == False{}: Bool},
      Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)),
      ne,
      Equal.trans(
        Bool,
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)),
        Bool.and(Ledgers.Line.is_eq(c2, c2), Nat.is_eq(j, j)),
        True{},
        Equal.sym(
          Bool,
          Bool.and(Ledgers.Line.is_eq(c2, c2), Nat.is_eq(j, j)),
          Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)),
          Equal.cong(
            Types.Fact,
            Bool,
            f => Fact.is_at(f, c2, j),
            Types.Fact.Vote{v, Types.Step.At{c2, j}, q},
            Types.Fact.Vote{name, Types.Step.At{c, k}, pk},
            Coded.Fact.is_eq_sound(
              Types.Fact.Vote{v, Types.Step.At{c2, j}, q},
              Types.Fact.Vote{name, Types.Step.At{c, k}, pk}
            )(et)
          )
        ),
        Shared.Bool.and_both(Ledgers.Line.is_eq(c2, c2), Nat.is_eq(j, j))(Ledgers.Line.is_eq_refl(c2))(
          Shared.Nat.is_eq_refl(j)
        )
      )
    ),
    ef => {==}
  )

# an ask is no vote
def Fact.ask_ne(+b: Types.Ask, +v: String, +st: Types.Step, +pk: Types.Pick) -> {
  Coded.Fact.is_eq(Types.Fact.Ask{b}, Types.Fact.Vote{v, st, pk}) == False{}: Bool
}:
  Lists.Bool.by(
    x => {x == False{}: Bool},
    Coded.Fact.is_eq(Types.Fact.Ask{b}, Types.Fact.Vote{v, st, pk}),
    et => Equal.cong(
      Types.Fact,
      Bool,
      f => Fact.is_ask(f),
      Types.Fact.Ask{b},
      Types.Fact.Vote{v, st, pk},
      Coded.Fact.is_eq_sound(Types.Fact.Ask{b}, Types.Fact.Vote{v, st, pk})(et)
    ),
    ef => {==}
  )

# after the node adds d, the facts hold the votes for a slot that d is no
# vote for as before
def Delta.votes(d: Delta, +s: Facts.Facts(), +v: String, +c2: Ledgers.Line, +j: Nat, +q: Types.Pick) -> {
  Delta.keeps(d, c2, j) == True{}: Bool
} -> {
  Facts.Facts.has(Delta.to(d, s), Types.Fact.Vote{v, Types.Step.At{c2, j}, q})
    == Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c2, j}, q}): Bool
}:
  match d:
    case Delta.Ask{+name, +a}:
      h => Facts.Facts.take_ask_votes(name, s, a, v, c2, j, q)
    case Delta.Vote{+name, +c, +k, +pk}:
      h => (
        %Fact.vote_ne(v, c2, j, q, name, c, k, pk)(
          Shared.Bool.not_true(Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(j, k)))(h)
        ): {
          Facts.Facts.has(
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}),
            Types.Fact.Vote{v, Types.Step.At{c2, j}, q}
          )
            == Bool.or(_, Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c2, j}, q})): Bool
        }
        Facts.Facts.has_add(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k}, pk},
          Types.Fact.Vote{v, Types.Step.At{c2, j}, q}
        )
      )

# an ask that starts a store is of a request that starts one
def Ask.starts_start(+h: Hashes.Hash, a: Types.Ask) -> {Facts.Ask.starts(h, a) == True{}: Bool} -> {
  Facts.Request.is_start(Lines.Ask.request(a)) == True{}: Bool
}:
  match a:
    case Types.Ask{+i, k, +r}:
      e => Shared.Bool.and_true_left(
        Facts.Request.is_start(r),
        Hashes.Hash.is_eq(Facts.Start.root(i, r), h)
      )(e)

# after the node adds a d that starts no store, the facts hold the asks that
# start a store as before
def Delta.asks(d: Delta, +s: Facts.Facts(), +h: Hashes.Hash, +b: Types.Ask) -> {Delta.ok(d) == True{}: Bool} -> {
  Facts.Ask.starts(h, b) == True{}: Bool
} -> {
  Facts.Facts.has(Delta.to(d, s), Types.Fact.Ask{b}) == Facts.Facts.has(s, Types.Fact.Ask{b}): Bool
}:
  match d:
    case Delta.Ask{+name, +a}:
      +ok => +st => Lists.Bool.by(
        x => {
          Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{b})
            == Bool.or(x, Facts.Facts.has(s, Types.Fact.Ask{b})): Bool
        } -> {
          Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{b})
            == Facts.Facts.has(s, Types.Fact.Ask{b}): Bool
        },
        Coded.Ask.is_eq(b, a),
        et => e => Lists.Bool.clash(
          {
            Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{b})
              == Facts.Facts.has(s, Types.Fact.Ask{b}): Bool
          },
          Facts.Request.is_start(Lines.Ask.request(a)),
          Shared.Bool.not_true(Facts.Request.is_start(Lines.Ask.request(a)))(ok),
          (
            %Coded.Ask.is_eq_sound(b, a)(et): {Facts.Request.is_start(Lines.Ask.request(_)) == True{}: Bool}
            Ask.starts_start(h, b)(st)
          )
        ),
        ef => e => e
      )(Facts.Facts.take_ask_asks(name, s, a, b))
    case Delta.Vote{+name, +c, +k, +pk}:
      ok => st => (
        %Fact.ask_ne(b, name, Types.Step.At{c, k}, pk): {
          Facts.Facts.has(
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}),
            Types.Fact.Ask{b}
          )
            == Bool.or(_, Facts.Facts.has(s, Types.Fact.Ask{b})): Bool
        }
        Facts.Facts.has_add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}, Types.Fact.Ask{b})
      )

# the facts before and after the node adds d hold the votes for a slot that d
# is no vote for alike
def Delta.votes_side(
  d: Delta,
  +s: Facts.Facts(),
  f: Bool,
  +v: String,
  +c2: Ledgers.Line,
  +j: Nat,
  +q: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{v, Types.Step.At{c2, j}, q})
    == Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c2, j}, q}): Bool
}:
  match f:
    case True{}:
      h => Delta.votes(d, s, v, c2, j, q)(h)
    case False{}:
      h => Equal.sym(
        Bool,
        Facts.Facts.has(Delta.to(d, s), Types.Fact.Vote{v, Types.Step.At{c2, j}, q}),
        Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c2, j}, q}),
        Delta.votes(d, s, v, c2, j, q)(h)
      )

# the facts before and after the node adds a d that starts no store hold the
# asks that start a store alike
def Delta.asks_side(d: Delta, +s: Facts.Facts(), f: Bool, +h: Hashes.Hash, +b: Types.Ask) -> {
  Delta.ok(d) == True{}: Bool
} -> {Facts.Ask.starts(h, b) == True{}: Bool} -> {
  Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Ask{b})
    == Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{b}): Bool
}:
  match f:
    case True{}:
      ok => st => Delta.asks(d, s, h, b)(ok)(st)
    case False{}:
      ok => st => Equal.sym(
        Bool,
        Facts.Facts.has(Delta.to(d, s), Types.Fact.Ask{b}),
        Facts.Facts.has(s, Types.Fact.Ask{b}),
        Delta.asks(d, s, h, b)(ok)(st)
      )

# Decided slots
# -------------

# the nodes ds that voted for the pick q at a slot that d is no vote for are
# as many before and after the node adds d
def Count.kept(
  ds: List<&2, String>,
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +q: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lists.List.count(
    ~String,
    ~Lines.Voting,
    ~Lines.Voting.voted,
    ds,
    Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, q}
  )
    == Lists.List.count(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ds,
      Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, q}
    ): Nat
}:
  match ds:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      +h => (
        %Delta.votes_side(d, s, f, x, c2, j, q)(h): {
          Shared.Nat.add_if(
            Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{x, Types.Step.At{c2, j}, q}),
            Lists.List.count(
              ~String,
              ~Lines.Voting,
              ~Lines.Voting.voted,
              r,
              Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, q}
            )
          )
            == Shared.Nat.add_if(
              _,
              Lists.List.count(
                ~String,
                ~Lines.Voting,
                ~Lines.Voting.voted,
                r,
                Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, q}
              )
            ): Nat
        }
        %Count.kept(r, d, s, f, c2, j, q)(h): {
          Shared.Nat.add_if(
            Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{x, Types.Step.At{c2, j}, q}),
            Lists.List.count(
              ~String,
              ~Lines.Voting,
              ~Lines.Voting.voted,
              r,
              Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, q}
            )
          )
            == Shared.Nat.add_if(
              Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{x, Types.Step.At{c2, j}, q}),
              _
            ): Nat
        }
        {==}
      )

# more than half of the nodes ds voted for the pick q at a slot that d is no
# vote for before the node adds d exactly when they did after
def Most.kept(
  +ds: List<&2, String>,
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +q: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, q})
    == Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, q}): Bool
}:
  h => Equal.cong(
    Nat,
    Bool,
    n => Lists.Nat.most(List.length(&2, String, ds), n),
    Lists.List.count(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ds,
      Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, q}
    ),
    Lists.List.count(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ds,
      Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, q}
    ),
    Count.kept(ds, d, s, f, c2, j, q)(h)
  )

# a member of xs is a member of xs with x before it, when it is kept
def Put.contains(x: Types.Pick, xs: List<&2, Types.Pick>, keep: Bool, y: Types.Pick) -> {
  List.contains(~Types.Pick, ~Coded.Pick.is_eq, xs, y) == True{}: Bool
} -> {List.contains(~Types.Pick, ~Coded.Pick.is_eq, List.filter.put(Types.Pick, x, xs, keep), y) == True{}: Bool}:
  match keep:
    case False{}:
      h => h
    case True{}:
      h => Shared.List.contains_cons(~Types.Pick, ~Coded.Pick.is_eq, x, xs, y)(h)

# a pick of the votes among r is a pick of the votes among f <> r
def Picks.cons(f: Types.Fact, +r: List<&2, Types.Fact>, +st: Types.Step, +pk: Types.Pick) -> {
  List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(r, st), pk) == True{}: Bool
} -> {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(f <> r, st), pk) == True{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      h => h
    case Types.Fact.Vote{v, st2, pk2}:
      h => Put.contains(pk2, Lines.Votes.picks(r, st), Coded.Step.is_eq(st2, st), pk)(h)

# the pick of a vote among fs for the step st is one of the picks for st
def Picks.in(fs: List<&2, Types.Fact>, +v: String, +st: Types.Step, +pk: Types.Pick) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, st, pk}) == True{}: Bool
} -> {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(fs, st), pk) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{+f, +r}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(f <> r, st), pk) == True{}: Bool},
        f,
        r,
        Types.Fact.Vote{v, st, pk},
        hin,
        ef => (
          %Equal.sym(Types.Fact, f, Types.Fact.Vote{v, st, pk}, ef): {
            List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(_ <> r, st), pk) == True{}: Bool
          }
          %Equal.sym(Bool, Coded.Step.is_eq(st, st), True{}, Coded.Step.is_eq_refl(st)): {
            List.contains(
              ~Types.Pick,
              ~Coded.Pick.is_eq,
              List.filter.put(Types.Pick, pk, Lines.Votes.picks(r, st), _),
              pk
            )
              == True{}: Bool
          }
          Lists.List.contains_head(~Types.Pick, ~Coded.Pick.is_eq, ~Coded.Pick.laws(), pk, Lines.Votes.picks(r, st))
        ),
        c => Picks.cons(f, r, st, pk)(Picks.in(r, v, st, pk)(c))
      )

# Most.in, with r a node that voted for the pick
def Most.in.of(
  +s: Facts.Facts(),
  +st: Types.Step,
  -ds: List<&2, String>,
  +o: Types.Pick,
  r: Exists(
    String,
    x => {
      List.contains(~String, ~String.eq, ds, x) == True{}: Bool
    }
      & {Lines.Voting.voted(Lines.Voting{s, st, o}, x) == True{}: Bool}
  )
) -> {
  List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(Facts.Facts.list(s), st), o) == True{}: Bool
}:
  (+v, w) = r
  (c, hv) = w
  Picks.in(Facts.Facts.list(s), v, st, o)(
    Equal.trans(
      Bool,
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{v, st, o}),
      Facts.Facts.has(s, Types.Fact.Vote{v, st, o}),
      True{},
      Equal.sym(
        Bool,
        Facts.Facts.has(s, Types.Fact.Vote{v, st, o}),
        List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{v, st, o}),
        Facts.Facts.has_list(s, Types.Fact.Vote{v, st, o})
      ),
      hv
    )
  )

# a pick that more than half of the nodes ds voted for at the step st is one
# of the picks for st
def Most.in(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +o: Types.Pick) -> {
  Lines.Voting.most(ds, Lines.Voting{s, st, o}) == True{}: Bool
} -> {
  List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(Facts.Facts.list(s), st), o) == True{}: Bool
}:
  m => Most.in.of(
    s,
    st,
    ds,
    o,
    Lists.List.count_pos(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ~String.eq,
      ~Texts.String.laws(),
      ds,
      Lines.Voting{s, st, o}
    )(
      Lists.Nat.most_pos(
        List.length(&2, String, ds),
        Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s, st, o})
      )(m)
    )
  )

# a pick that more than half of the nodes voted for is the pick that wins
def Wins.only(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick, +o: Types.Pick) -> {
  Lines.Tally.wins(Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk) == True{}: Bool
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, o}) == True{}: Bool} -> {o == pk: Types.Pick}:
  w => +m => (
    bt : {Bool.or(Coded.Pick.is_eq(o, pk), False{}) == True{}: Bool} = (
      %m: {Bool.or(Coded.Pick.is_eq(o, pk), Bool.not(_)) == True{}: Bool}
      Lists.List.holds_in(
        ~Types.Pick,
        ~Lines.Rival,
        ~Lines.Rival.beats,
        ~Coded.Pick.is_eq,
        ~Coded.Pick.laws(),
        Lines.Votes.picks(Facts.Facts.list(s), st),
        Lines.Rival{Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk},
        o
      )(
        Shared.Bool.and_true_right(
          Lines.Voting.most(ds, Lines.Voting{s, st, pk}),
          Shared.List.holds(
            ~Types.Pick,
            ~Lines.Rival,
            ~Lines.Rival.beats,
            Lines.Votes.picks(Facts.Facts.list(s), st),
            Lines.Rival{Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk}
          )
        )(w)
      )(Most.in(s, st, ds, o)(m))
    )
    Coded.Pick.is_eq_sound(o, pk)(
      Equal.trans(
        Bool,
        Coded.Pick.is_eq(o, pk),
        Bool.or(Coded.Pick.is_eq(o, pk), False{}),
        True{},
        Shared.Bool.or_false(Coded.Pick.is_eq(o, pk)),
        bt
      )
    )
  )

# no pick stands against the pick that wins a slot that d is no vote for,
# on the other side of d
def Beats.kept(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick,
  +X: List<&2, Types.Pick>,
  +o: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lines.Tally.wins(
    Lines.Tally{
      Delta.side(d, s, f),
      Types.Step.At{c2, j},
      ds,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j})
    },
    pk
  )
    == True{}: Bool
} -> {
  Lines.Rival.beats(Lines.Rival{Lines.Tally{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds, X}, pk}, o) == True{}: Bool
}:
  hk => w => Lists.Bool.by(
    x => {Bool.or(Coded.Pick.is_eq(o, pk), Bool.not(x)) == True{}: Bool},
    Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, o}),
    et => (
      %Wins.only(Delta.side(d, s, f), Types.Step.At{c2, j}, ds, pk, o)(w)(
        Equal.trans(
          Bool,
          Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, o}),
          Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, o}),
          True{},
          Most.kept(ds, d, s, f, c2, j, o)(hk),
          et
        )
      ): {Bool.or(Coded.Pick.is_eq(o, _), False{}) == True{}: Bool}
      %Equal.sym(Bool, Coded.Pick.is_eq(o, o), True{}, Coded.Pick.is_eq_refl(o)): {
        Bool.or(_, False{}) == True{}: Bool
      }
      {==}
    ),
    ef => Shared.Bool.or_true_right(Coded.Pick.is_eq(o, pk))
  )

# no pick of ys stands against the pick that wins a slot that d is no vote
# for, on the other side of d
def Holds.kept(
  ys: List<&2, Types.Pick>,
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick,
  +X: List<&2, Types.Pick>
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lines.Tally.wins(
    Lines.Tally{
      Delta.side(d, s, f),
      Types.Step.At{c2, j},
      ds,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j})
    },
    pk
  )
    == True{}: Bool
} -> {
  Shared.List.holds(
    ~Types.Pick,
    ~Lines.Rival,
    ~Lines.Rival.beats,
    ys,
    Lines.Rival{Lines.Tally{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds, X}, pk}
  )
    == True{}: Bool
}:
  match ys:
    case Nil{}:
      hk => w => {==}
    case Con{+y, +r}:
      +hk => +w => Shared.List.all.if_both(
        Lines.Rival.beats(Lines.Rival{Lines.Tally{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds, X}, pk}, y),
        u => Shared.List.holds(
          ~Types.Pick,
          ~Lines.Rival,
          ~Lines.Rival.beats,
          r,
          Lines.Rival{Lines.Tally{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds, X}, pk}
        )
      )(Beats.kept(d, s, f, c2, j, ds, pk, X, y)(hk)(w))(Holds.kept(r, d, s, f, c2, j, ds, pk, X)(hk)(w))

# the pick that wins a slot that d is no vote for wins it on the other side
# of d
def Wins.kept(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lines.Tally.wins(
    Lines.Tally{
      Delta.side(d, s, f),
      Types.Step.At{c2, j},
      ds,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j})
    },
    pk
  )
    == True{}: Bool
} -> {
  Lines.Tally.wins(
    Lines.Tally{
      Delta.side(d, s, Bool.not(f)),
      Types.Step.At{c2, j},
      ds,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), Types.Step.At{c2, j})
    },
    pk
  )
    == True{}: Bool
}:
  +hk => +w => Shared.Bool.and_both(
    Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, pk}),
    Shared.List.holds(
      ~Types.Pick,
      ~Lines.Rival,
      ~Lines.Rival.beats,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), Types.Step.At{c2, j}),
      Lines.Rival{
        Lines.Tally{
          Delta.side(d, s, Bool.not(f)),
          Types.Step.At{c2, j},
          ds,
          Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), Types.Step.At{c2, j})
        },
        pk
      }
    )
  )(
    Equal.trans(
      Bool,
      Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, pk}),
      Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, pk}),
      True{},
      Equal.sym(
        Bool,
        Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, pk}),
        Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, pk}),
        Most.kept(ds, d, s, f, c2, j, pk)(hk)
      ),
      Shared.Bool.and_true_left(
        Lines.Voting.most(ds, Lines.Voting{Delta.side(d, s, f), Types.Step.At{c2, j}, pk}),
        Shared.List.holds(
          ~Types.Pick,
          ~Lines.Rival,
          ~Lines.Rival.beats,
          Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j}),
          Lines.Rival{
            Lines.Tally{
              Delta.side(d, s, f),
              Types.Step.At{c2, j},
              ds,
              Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j})
            },
            pk
          }
        )
      )(w)
    )
  )(
    Holds.kept(
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), Types.Step.At{c2, j}),
      d,
      s,
      f,
      c2,
      j,
      ds,
      pk,
      Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), Types.Step.At{c2, j})
    )(hk)(w)
  )

# more than half of the nodes voted for the pick that wins
def Wins.most(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Lines.Tally.wins(Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk) == True{}: Bool
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, pk}) == True{}: Bool}:
  w => Shared.Bool.and_true_left(
    Lines.Voting.most(ds, Lines.Voting{s, st, pk}),
    Shared.List.holds(
      ~Types.Pick,
      ~Lines.Rival,
      ~Lines.Rival.beats,
      Lines.Votes.picks(Facts.Facts.list(s), st),
      Lines.Rival{Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk}
    )
  )(w)

# a pick that wins the step st is what the nodes ds decided for st
def Wins.decided(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Lines.Tally.wins(Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk) == True{}: Bool
} -> {Lines.Votes.decided(s, st, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  +w => Lists.List.pick_one(
    ~Types.Pick,
    ~Lines.Tally,
    ~Lines.Tally.wins,
    ~Coded.Pick.is_eq,
    ~Coded.Pick.laws(),
    Lines.Votes.picks(Facts.Facts.list(s), st),
    Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)},
    pk
  )(Most.in(s, st, ds, pk)(Wins.most(s, st, ds, pk)(w)))(w)(
    +y => hy => wy => Equal.sym(
      Types.Pick,
      pk,
      y,
      Wins.only(s, st, ds, y, pk)(wy)(Wins.most(s, st, ds, pk)(w))
    )
  )

# what the nodes ds decided for a slot that d is no vote for, they decided
# on the other side of d
def Decided.kept(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c2: Ledgers.Line,
  +j: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick
) -> {Delta.keeps(d, c2, j) == True{}: Bool} -> {
  Lines.Votes.decided(Delta.side(d, s, f), Types.Step.At{c2, j}, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {
  Lines.Votes.decided(Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds) == Some{pk}: Maybe<&2, Types.Pick>
}:
  hk => e => Wins.decided(Delta.side(d, s, Bool.not(f)), Types.Step.At{c2, j}, ds, pk)(
    Wins.kept(d, s, f, c2, j, ds, pk)(hk)(
      Lists.List.pick_hit(
        ~Types.Pick,
        ~Lines.Tally,
        ~Lines.Tally.wins,
        Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j}),
        Lines.Tally{
          Delta.side(d, s, f),
          Types.Step.At{c2, j},
          ds,
          Lines.Votes.picks(Facts.Facts.list(Delta.side(d, s, f)), Types.Step.At{c2, j})
        },
        pk
      )(e)
    )
  )

# after the node adds d, the nodes ds decided for a slot that d is no vote
# for what they decided before
def Decided.same(+d: Delta, +s: Facts.Facts(), +c2: Ledgers.Line, +j: Nat, +ds: List<&2, String>) -> {
  Delta.keeps(d, c2, j) == True{}: Bool
} -> {
  Lines.Votes.decided(Delta.to(d, s), Types.Step.At{c2, j}, ds)
    == Lines.Votes.decided(s, Types.Step.At{c2, j}, ds): Maybe<&2, Types.Pick>
}:
  +hk => Lists.Maybe.by(
    Types.Pick,
    m => {Lines.Votes.decided(Delta.to(d, s), Types.Step.At{c2, j}, ds) == m: Maybe<&2, Types.Pick>},
    Lines.Votes.decided(s, Types.Step.At{c2, j}, ds),
    +en => Lists.Maybe.by(
      Types.Pick,
      m => {m == None{}: Maybe<&2, Types.Pick>},
      Lines.Votes.decided(Delta.to(d, s), Types.Step.At{c2, j}, ds),
      en2 => {==},
      +y => ey => Equal.trans(
        Maybe<&2, Types.Pick>,
        Some{y},
        Lines.Votes.decided(s, Types.Step.At{c2, j}, ds),
        None{},
        Equal.sym(
          Maybe<&2, Types.Pick>,
          Lines.Votes.decided(s, Types.Step.At{c2, j}, ds),
          Some{y},
          Decided.kept(d, s, True{}, c2, j, ds, y)(hk)(ey)
        ),
        en
      )
    ),
    +x => ex => Decided.kept(d, s, False{}, c2, j, ds, x)(hk)(ex)
  )

# The bound of the slots
# ----------------------

# a d that is no vote for a slot of a line is no vote for each slot of it
def Delta.spares_keeps(d: Delta, c2: Ledgers.Line, j: Nat) -> {Delta.spares(d, c2) == True{}: Bool} -> {
  Delta.keeps(d, c2, j) == True{}: Bool
}:
  match d:
    case Delta.Ask{name, a}:
      h => {==}
    case Delta.Vote{name, c, k, pk}:
      h => (
        %Equal.sym(
          Bool,
          Ledgers.Line.is_eq(c2, c),
          False{},
          Shared.Bool.not_true(Ledgers.Line.is_eq(c2, c))(h)
        ): {Bool.not(Bool.and(_, Nat.is_eq(j, k))) == True{}: Bool}
        {==}
      )

# the bound of a line is at least 1
def Bound.pos(fs: List<&2, Types.Fact>, +c: Ledgers.Line) -> {
  Nat.is_le(1n, Lines.Line.bound(fs, c)) == True{}: Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{a}, rest}:
      Bound.pos(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, pk}, rest}:
      Bound.pos(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.At{+c2, +k}, pk}, +rest}:
      Shared.Nat.le_trans(
        1n,
        Lines.Line.bound(rest, c),
        Nat.max(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(rest, c))
      )(Bound.pos(rest, c))(
        Lists.Nat.le_max_right(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(rest, c))
      )

# what is at most the bound that r gives is at most the bound that f <> r gives
def Bound.cons(f: Types.Fact, +r: List<&2, Types.Fact>, +c: Ledgers.Line, +n: Nat) -> {
  Nat.is_le(n, Lines.Line.bound(r, c)) == True{}: Bool
} -> {Nat.is_le(n, Lines.Line.bound(f <> r, c)) == True{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      h => h
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      h => h
    case Types.Fact.Vote{v, Types.Step.At{+c2, +k}, pk}:
      h => Shared.Nat.le_trans(
        n,
        Lines.Line.bound(r, c),
        Nat.max(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(r, c))
      )(h)(Lists.Nat.le_max_right(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(r, c)))

# the bound of a line is above each slot of it that a vote is for
def Bound.ge(fs: List<&2, Types.Fact>, +c: Ledgers.Line, +v: String, +k: Nat, +pk: Types.Pick) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}) == True{}: Bool
} -> {Nat.is_le(1n+k, Lines.Line.bound(fs, c)) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => Empty.absurd({Nat.is_le(1n+k, 1n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{+f, +r}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {Nat.is_le(1n+k, Lines.Line.bound(f <> r, c)) == True{}: Bool},
        f,
        r,
        Types.Fact.Vote{v, Types.Step.At{c, k}, pk},
        hin,
        ef => (
          %Equal.sym(Types.Fact, f, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}, ef): {
            Nat.is_le(1n+k, Lines.Line.bound(_ <> r, c)) == True{}: Bool
          }
          %Equal.sym(Bool, Ledgers.Line.is_eq(c, c), True{}, Ledgers.Line.is_eq_refl(c)): {
            Nat.is_le(1n+k, Nat.max(Lines.Line.bound.at(_, k), Lines.Line.bound(r, c))) == True{}: Bool
          }
          Lists.Nat.le_max_left(1n+k, Lines.Line.bound(r, c))
        ),
        cin => Bound.cons(f, r, c, 1n+k)(Bound.ge(r, c, v, k, pk)(cin))
      )

# the greater of two numbers is one of them
def Nat.max_either.up(-a: Nat, -b: Nat, -m: Nat, r: {m == a: Nat} | {m == b: Nat}) -> {1n+m == 1n+a: Nat}
  | {1n+m == 1n+b: Nat}:
  match r:
    case Inl{e}:
      Inl{Equal.cong(Nat, Nat, n => 1n+n, m, a, e)}
    case Inr{e}:
      Inr{Equal.cong(Nat, Nat, n => 1n+n, m, b, e)}

# the greater of two numbers is one of them
def Nat.max_either(a: Nat, b: Nat) -> {Nat.max(a, b) == a: Nat} | {Nat.max(a, b) == b: Nat}:
  match a b:
    case 0n _:
      Inr{{==}}
    case 1n+ap 0n:
      Inl{{==}}
    case 1n+(+ap) 1n+(+bp):
      Nat.max_either.up(ap, bp, Nat.max(ap, bp), Nat.max_either(ap, bp))

# n is 1, or one more than a slot of the line c that a vote among fs is for
def Bound.Is(fs: List<&2, Types.Fact>, c: Ledgers.Line, n: Nat) -> Type:
  {
    n == 1n: Nat
  }
    | Exists(
      String,
      v => Exists(
        Nat,
        k => Exists(
          Types.Pick,
          pk => {
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}) == True{}: Bool
          }
            & {n == 1n+k: Nat}
        )
      )
    )

# what the votes among r make n, the votes among f <> r make it
def Bound.is_cons(+f: Types.Fact, +r: List<&2, Types.Fact>, +c: Ledgers.Line, -n: Nat, ih: Bound.Is(r, c, n)) -> Bound.Is(
  f <> r,
  c,
  n
):
  match ih:
    case Inl{e}:
      Inl{e}
    case Inr{w}:
      (+v, w2) = w
      (+k, w3) = w2
      (+pk, w4) = w3
      (cin, eb) = w4
      Inr{
        (
          v,
          (
            k,
            (
              pk,
              (
                Shared.List.contains_cons(
                  ~Types.Fact,
                  ~Coded.Fact.is_eq,
                  f,
                  r,
                  Types.Fact.Vote{v, Types.Step.At{c, k}, pk}
                )(cin),
                eb
              )
            )
          )
        )
      }

# Bound.is_at, once the greater of the two numbers is known to be one of them
def Bound.is_at.of(
  +v: String,
  +c2: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  +r: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  -m: Nat,
  e: {c2 == c: Ledgers.Line},
  x: {m == 1n+k: Nat} | {m == Lines.Line.bound(r, c): Nat},
  ih: Bound.Is(r, c, Lines.Line.bound(r, c))
) -> Bound.Is(Types.Fact.Vote{v, Types.Step.At{c2, k}, pk} <> r, c, m):
  match x:
    case Inl{em}:
      Inr{
        (
          v,
          (
            k,
            (
              pk,
              (
                (
                  %e: {
                    List.contains(
                      ~Types.Fact,
                      ~Coded.Fact.is_eq,
                      Types.Fact.Vote{v, Types.Step.At{c2, k}, pk} <> r,
                      Types.Fact.Vote{v, Types.Step.At{_, k}, pk}
                    )
                      == True{}: Bool
                  }
                  Lists.List.contains_head(
                    ~Types.Fact,
                    ~Coded.Fact.is_eq,
                    ~Coded.Fact.laws(),
                    Types.Fact.Vote{v, Types.Step.At{c2, k}, pk},
                    r
                  )
                ),
                em
              )
            )
          )
        )
      }
    case Inr{em}:
      %Equal.sym(Nat, m, Lines.Line.bound(r, c), em): Bound.Is(
        Types.Fact.Vote{v, Types.Step.At{c2, k}, pk} <> r,
        c,
        _
      )
      Bound.is_cons(Types.Fact.Vote{v, Types.Step.At{c2, k}, pk}, r, c, Lines.Line.bound(r, c), ih)

# the bound of a line is 1, or one more than a slot of it that a vote is for
def Bound.is(fs: List<&2, Types.Fact>, +c: Ledgers.Line) -> Bound.Is(fs, c, Lines.Line.bound(fs, c)):
  match fs:
    case Nil{}:
      Inl{{==}}
    case Con{Types.Fact.Ask{+a}, +rest}:
      Bound.is_cons(Types.Fact.Ask{a}, rest, c, Lines.Line.bound(rest, c), Bound.is(rest, c))
    case Con{Types.Fact.Vote{+v, Types.Step.Broken{}, +pk}, +rest}:
      Bound.is_cons(
        Types.Fact.Vote{v, Types.Step.Broken{}, pk},
        rest,
        c,
        Lines.Line.bound(rest, c),
        Bound.is(rest, c)
      )
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k}, +pk}, +rest}:
      Lists.Bool.by(
        hit => {Ledgers.Line.is_eq(c2, c) == hit: Bool} -> Bound.Is(
          Types.Fact.Vote{v, Types.Step.At{c2, k}, pk} <> rest,
          c,
          Nat.max(Lines.Line.bound.at(hit, k), Lines.Line.bound(rest, c))
        ),
        Ledgers.Line.is_eq(c2, c),
        et => eh => Bound.is_at.of(
          v,
          c2,
          k,
          pk,
          rest,
          c,
          Nat.max(1n+k, Lines.Line.bound(rest, c)),
          Ledgers.Line.is_eq_sound(c2, c)(eh),
          Nat.max_either(1n+k, Lines.Line.bound(rest, c)),
          Bound.is(rest, c)
        ),
        ef => eh => Bound.is_cons(
          Types.Fact.Vote{v, Types.Step.At{c2, k}, pk},
          rest,
          c,
          Lines.Line.bound(rest, c),
          Bound.is(rest, c)
        )
      )({==})

# Bound.le, with what makes the bound n on one side of d
def Bound.le.of(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +c: Ledgers.Line,
  -n: Nat,
  r: Bound.Is(Facts.Facts.list(Delta.side(d, s, f)), c, n),
  hs: {Delta.spares(d, c) == True{}: Bool}
) -> {Nat.is_le(n, Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c)) == True{}: Bool}:
  match r:
    case Inl{e}:
      %Equal.sym(Nat, n, 1n, e): {
        Nat.is_le(_, Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c)) == True{}: Bool
      }
      Bound.pos(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c)
    case Inr{w}:
      (+v, w2) = w
      (+k, w3) = w2
      (+pk, w4) = w3
      (cin, eb) = w4
      %Equal.sym(Nat, n, 1n+k, eb): {
        Nat.is_le(_, Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c)) == True{}: Bool
      }
      Bound.ge(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c, v, k, pk)(
        Equal.trans(
          Bool,
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Facts.Facts.list(Delta.side(d, s, Bool.not(f))),
            Types.Fact.Vote{v, Types.Step.At{c, k}, pk}
          ),
          Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
          True{},
          Equal.sym(
            Bool,
            Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
            List.contains(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Facts.Facts.list(Delta.side(d, s, Bool.not(f))),
              Types.Fact.Vote{v, Types.Step.At{c, k}, pk}
            ),
            Facts.Facts.has_list(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c, k}, pk})
          ),
          Equal.trans(
            Bool,
            Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
            Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
            True{},
            Equal.sym(
              Bool,
              Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
              Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
              Delta.votes_side(d, s, f, v, c, k, pk)(Delta.spares_keeps(d, c, k)(hs))
            ),
            Equal.trans(
              Bool,
              Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
              List.contains(
                ~Types.Fact,
                ~Coded.Fact.is_eq,
                Facts.Facts.list(Delta.side(d, s, f)),
                Types.Fact.Vote{v, Types.Step.At{c, k}, pk}
              ),
              True{},
              Facts.Facts.has_list(Delta.side(d, s, f), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
              cin
            )
          )
        )
      )

# the bound of a line that d is no vote for a slot of is no greater on the
# other side of d
def Bound.le(+d: Delta, +s: Facts.Facts(), +f: Bool, +c: Ledgers.Line) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Nat.is_le(
    Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, f)), c),
    Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), c)
  )
    == True{}: Bool
}:
  hs => Bound.le.of(
    d,
    s,
    f,
    c,
    Lines.Line.bound(Facts.Facts.list(Delta.side(d, s, f)), c),
    Bound.is(Facts.Facts.list(Delta.side(d, s, f)), c),
    hs
  )

# after the node adds d, the bound of a line that d is no vote for a slot of
# is as before
def Bound.same(+d: Delta, +s: Facts.Facts(), +c: Ledgers.Line) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c) == Lines.Line.bound(Facts.Facts.list(s), c): Nat
}:
  +hs => Shared.Nat.is_eq_sound(
    Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c),
    Lines.Line.bound(Facts.Facts.list(s), c)
  )(
    Equal.trans(
      Bool,
      Nat.is_eq(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), Lines.Line.bound(Facts.Facts.list(s), c)),
      Bool.and(
        Nat.is_le(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), Lines.Line.bound(Facts.Facts.list(s), c)),
        Nat.is_le(Lines.Line.bound(Facts.Facts.list(s), c), Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c))
      ),
      True{},
      Equal.sym(
        Bool,
        Bool.and(
          Nat.is_le(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), Lines.Line.bound(Facts.Facts.list(s), c)),
          Nat.is_le(Lines.Line.bound(Facts.Facts.list(s), c), Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c))
        ),
        Nat.is_eq(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), Lines.Line.bound(Facts.Facts.list(s), c)),
        Shared.Nat.le_both(
          Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c),
          Lines.Line.bound(Facts.Facts.list(s), c)
        )
      ),
      Shared.Bool.and_both(
        Nat.is_le(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), Lines.Line.bound(Facts.Facts.list(s), c)),
        Nat.is_le(Lines.Line.bound(Facts.Facts.list(s), c), Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c))
      )(Bound.le(d, s, True{}, c)(hs))(Bound.le(d, s, False{}, c)(hs))
    )
  )

