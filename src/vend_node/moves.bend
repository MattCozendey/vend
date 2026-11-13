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

import ./versions.bend as Versions

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

# Version 0
# ---------

# a list is within itself
def List.within_refl(~A: Data, ~same: A -> A -> Bool, ~laws: Shared.Eq.Laws(A, same), xs: List<&2, A>) -> {
  Shared.List.within(~A, ~same, xs, xs) == True{}: Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(List.contains(~A, ~same, x <> r, x), Shared.List.within(~A, ~same, r, x <> r))(
        Lists.List.contains_head(~A, ~same, ~laws, x, r)
      )(Lists.List.within_cons(~A, ~same, r, x, r)(List.within_refl(~A, ~same, ~laws, r)))

# when List.pick gives nothing, p(g) holds of no member of xs
def List.pick_miss(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {Lists.List.pick(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, A>} -> {
  List.contains(~A, ~same, xs, x) == True{}: Bool
} -> {p(g)(x) == False{}: Bool}:
  match xs:
    case Nil{}:
      e => hin => Empty.absurd({p(g)(x) == False{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +r}:
      Lists.Bool.by(
        hit => {p(g)(h) == hit: Bool} -> {
          List.find.if(A, h, u => Lists.List.pick(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, A>
        } -> {List.contains(~A, ~same, h <> r, x) == True{}: Bool} -> {p(g)(x) == False{}: Bool},
        p(g)(h),
        et => eh => e => hin => Empty.absurd({p(g)(x) == False{}: Bool}, Lists.Maybe.some_ne_none(A, h, e)),
        ef => eh => e => hin => Lists.List.contains_cons_by(
          ~A,
          ~same,
          ~laws,
          {p(g)(x) == False{}: Bool},
          h,
          r,
          x,
          hin,
          ex => (
            %ex: {p(g)(_) == False{}: Bool}
            eh
          ),
          cin => List.pick_miss(~A, ~V, ~p, ~same, ~laws, r, g, x)(e)(cin)
        )
      )({==})

# a member of xs is a member of xs with x before it, when it is kept
def Asks.put_contains(x: Types.Ask, xs: List<&2, Types.Ask>, keep: Bool, y: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, xs, y) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, x, xs, keep), y) == True{}: Bool}:
  match keep:
    case False{}:
      h => h
    case True{}:
      h => Shared.List.contains_cons(~Types.Ask, ~Coded.Ask.is_eq, x, xs, y)(h)

# a start among r is a start among f <> r
def Starts.cons(f: Types.Fact, +r: List<&2, Types.Fact>, +h: Hashes.Hash, +a: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(r, h), a) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(f <> r, h), a) == True{}: Bool}:
  match f:
    case Types.Fact.Vote{v, st, pk}:
      e => e
    case Types.Fact.Ask{+b}:
      e => Asks.put_contains(b, Lines.Starts.of(r, h), Facts.Ask.starts(h, b), a)(e)

# an ask among fs that starts the store of h is one of its starts
def Starts.in(fs: List<&2, Types.Fact>, +h: Hashes.Hash, +a: Types.Ask) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
} -> {Facts.Ask.starts(h, a) == True{}: Bool} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(fs, h), a) == True{}: Bool
}:
  match fs:
    case Nil{}:
      hin => st => hin
    case Con{+f, +r}:
      hin => +st => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(f <> r, h), a) == True{}: Bool},
        f,
        r,
        Types.Fact.Ask{a},
        hin,
        ef => (
          %Equal.sym(Types.Fact, f, Types.Fact.Ask{a}, ef): {
            List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(_ <> r, h), a) == True{}: Bool
          }
          %Equal.sym(Bool, Facts.Ask.starts(h, a), True{}, st): {
            List.contains(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              List.filter.put(Types.Ask, a, Lines.Starts.of(r, h), _),
              a
            )
              == True{}: Bool
          }
          Lists.List.contains_head(~Types.Ask, ~Coded.Ask.is_eq, ~Coded.Ask.laws(), a, Lines.Starts.of(r, h))
        ),
        cin => Starts.cons(f, r, h, a)(Starts.in(r, h, a)(cin)(st))
      )

# Starts.out for f <> r, from Starts.out for r
def Starts.out.up(
  +f: Types.Fact,
  +r: List<&2, Types.Fact>,
  +h: Hashes.Hash,
  +a: Types.Ask,
  p: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, r, Types.Fact.Ask{a}) == True{}: Bool
  }
    & {Facts.Ask.starts(h, a) == True{}: Bool}
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, f <> r, Types.Fact.Ask{a}) == True{}: Bool
}
  & {Facts.Ask.starts(h, a) == True{}: Bool}:
  (c, e) = p
  (Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, f, r, Types.Fact.Ask{a})(c), e)

# a start of the store of h among fs is an ask among fs that starts it
def Starts.out(fs: List<&2, Types.Fact>, +h: Hashes.Hash, +a: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(fs, h), a) == True{}: Bool
} -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
}
  & {Facts.Ask.starts(h, a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => Empty.absurd(
        {
          List.contains(~Types.Fact, ~Coded.Fact.is_eq, [], Types.Fact.Ask{a}) == True{}: Bool
        }
          & {Facts.Ask.starts(h, a) == True{}: Bool},
        Shared.Bool.false_ne_true(hin)
      )
    case Con{Types.Fact.Vote{+v, +st, +pk}, +r}:
      hin => Starts.out.up(Types.Fact.Vote{v, st, pk}, r, h, a, Starts.out(r, h, a)(hin))
    case Con{Types.Fact.Ask{+b}, +r}:
      Lists.Bool.by(
        hit => {Facts.Ask.starts(h, b) == hit: Bool} -> {
          List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, b, Lines.Starts.of(r, h), hit), a) == True{}: Bool
        } -> {
          List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> r, Types.Fact.Ask{a}) == True{}: Bool
        }
          & {Facts.Ask.starts(h, a) == True{}: Bool},
        Facts.Ask.starts(h, b),
        et => es => hin => Lists.List.contains_cons_by(
          ~Types.Ask,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          {
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> r, Types.Fact.Ask{a}) == True{}: Bool
          }
            & {Facts.Ask.starts(h, a) == True{}: Bool},
          b,
          Lines.Starts.of(r, h),
          a,
          hin,
          eb => (
            %eb: {
              List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> r, Types.Fact.Ask{_}) == True{}: Bool
            }
              & {Facts.Ask.starts(h, _) == True{}: Bool}
            (Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Ask{b}, r), es)
          ),
          cin => Starts.out.up(Types.Fact.Ask{b}, r, h, a, Starts.out(r, h, a)(cin))
        ),
        ef => es => hin => Starts.out.up(Types.Fact.Ask{b}, r, h, a, Starts.out(r, h, a)(hin))
      )({==})

# Starts.kept, with p what Starts.out gives
def Starts.kept.of(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +h: Hashes.Hash,
  +x: Types.Ask,
  ok: {Delta.ok(d) == True{}: Bool},
  p: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(Delta.side(d, s, f)), Types.Fact.Ask{x}) == True{}: Bool
  }
    & {Facts.Ask.starts(h, x) == True{}: Bool}
) -> {
  List.contains(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
    x
  )
    == True{}: Bool
}:
  (c, +st) = p
  Starts.in(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h, x)(
    Equal.trans(
      Bool,
      List.contains(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Facts.Facts.list(Delta.side(d, s, Bool.not(f))),
        Types.Fact.Ask{x}
      ),
      Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{x}),
      True{},
      Equal.sym(
        Bool,
        Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{x}),
        List.contains(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          Facts.Facts.list(Delta.side(d, s, Bool.not(f))),
          Types.Fact.Ask{x}
        ),
        Facts.Facts.has_list(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{x})
      ),
      Equal.trans(
        Bool,
        Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{x}),
        Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Ask{x}),
        True{},
        Equal.sym(
          Bool,
          Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Ask{x}),
          Facts.Facts.has(Delta.side(d, s, Bool.not(f)), Types.Fact.Ask{x}),
          Delta.asks_side(d, s, f, h, x)(ok)(st)
        ),
        Equal.trans(
          Bool,
          Facts.Facts.has(Delta.side(d, s, f), Types.Fact.Ask{x}),
          List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(Delta.side(d, s, f)), Types.Fact.Ask{x}),
          True{},
          Facts.Facts.has_list(Delta.side(d, s, f), Types.Fact.Ask{x}),
          c
        )
      )
    )
  )(st)

# a start of the store of h on one side of a d that starts no store is a start
# of it on the other side
def Starts.kept(+d: Delta, +s: Facts.Facts(), +f: Bool, +h: Hashes.Hash, +x: Types.Ask) -> {
  Delta.ok(d) == True{}: Bool
} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h), x) == True{}: Bool
} -> {
  List.contains(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
    x
  )
    == True{}: Bool
}:
  ok => hin => Starts.kept.of(d, s, f, h, x, ok, Starts.out(Facts.Facts.list(Delta.side(d, s, f)), h, x)(hin))

# a start of the store of h on the other side of a d that starts no store is
# a start of it on this side
def Starts.kept_back(+d: Delta, +s: Facts.Facts(), f: Bool, +h: Hashes.Hash, +x: Types.Ask) -> {
  Delta.ok(d) == True{}: Bool
} -> {
  List.contains(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
    x
  )
    == True{}: Bool
} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h), x) == True{}: Bool
}:
  match f:
    case True{}:
      ok => hin => Starts.kept(d, s, False{}, h, x)(ok)(hin)
    case False{}:
      ok => hin => Starts.kept(d, s, True{}, h, x)(ok)(hin)

# no ask of ys stands against an ask that leads the starts of the store of h,
# when ys is within the starts on the other side of a d that starts no store
def Leads.kept.go(
  ys: List<&2, Types.Ask>,
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +h: Hashes.Hash,
  +x: Types.Ask
) -> {Delta.ok(d) == True{}: Bool} -> {
  Lines.Ask.leads(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h), x) == True{}: Bool
} -> {
  Shared.List.within(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    ys,
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h)
  )
    == True{}: Bool
} -> {Shared.List.holds(~Types.Ask, ~Types.Ask, ~Lines.Ask.led, ys, x) == True{}: Bool}:
  match ys:
    case Nil{}:
      ok => l => w => {==}
    case Con{+y, +r}:
      +ok => +l => +w => Shared.List.all.if_both(
        Lines.Ask.led(x, y),
        u => Shared.List.holds(~Types.Ask, ~Types.Ask, ~Lines.Ask.led, r, x)
      )(
        Lists.List.holds_in(
          ~Types.Ask,
          ~Types.Ask,
          ~Lines.Ask.led,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
          x,
          y
        )(l)(
          Starts.kept_back(d, s, f, h, y)(ok)(
            Shared.Bool.and_true_left(
              List.contains(
                ~Types.Ask,
                ~Coded.Ask.is_eq,
                Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
                y
              ),
              Shared.List.within(
                ~Types.Ask,
                ~Coded.Ask.is_eq,
                r,
                Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h)
              )
            )(w)
          )
        )
      )(
        Leads.kept.go(r, d, s, f, h, x)(ok)(l)(
          Shared.Bool.and_true_right(
            List.contains(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
              y
            ),
            Shared.List.within(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              r,
              Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h)
            )
          )(w)
        )
      )

# an ask that leads the starts of the store of h leads them on the other side
# of a d that starts no store
def Leads.kept(+d: Delta, +s: Facts.Facts(), +f: Bool, +h: Hashes.Hash, +x: Types.Ask) -> {
  Delta.ok(d) == True{}: Bool
} -> {Lines.Ask.leads(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h), x) == True{}: Bool} -> {
  Lines.Ask.leads(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h), x) == True{}: Bool
}:
  ok => l => Leads.kept.go(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h), d, s, f, h, x)(ok)(
    l
  )(
    List.within_refl(
      ~Types.Ask,
      ~Coded.Ask.is_eq,
      ~Coded.Ask.laws(),
      Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h)
    )
  )

# two asks that do not stand against each other give one version 0
def Led.same(x: Types.Ask, y: Types.Ask) -> {Lines.Ask.led(x, y) == True{}: Bool} -> {
  Lines.Ask.led(y, x) == True{}: Bool
} -> {Lines.Store.first.of(Some{y}) == Lines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>}:
  match x y:
    case Types.Ask{+i, +k, +r} Types.Ask{+j, +l, +q}:
      h1 => h2 => Lists.Bool.by(
        a => {Bool.or(a, Nat.is_lt(l, k)) == True{}: Bool} -> {
          Bool.or(Bool.and(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r)), Nat.is_lt(k, l)) == True{}: Bool
        } -> {Some{Lines.Entry.first(j, q, 0n)} == Some{Lines.Entry.first(i, r, 0n)}: Maybe<&2, Types.Entry>},
        Bool.and(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q)),
        +et => g1 => g2 => (
          %Ledgers.Id.is_eq_sound(i, j)(
            Shared.Bool.and_true_left(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))(et)
          ): {Some{Lines.Entry.first(_, q, 0n)} == Some{Lines.Entry.first(i, r, 0n)}: Maybe<&2, Types.Entry>}
          %Coded.Request.is_eq_sound(r, q)(
            Shared.Bool.and_true_right(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))(et)
          ): {Some{Lines.Entry.first(i, _, 0n)} == Some{Lines.Entry.first(i, r, 0n)}: Maybe<&2, Types.Entry>}
          {==}
        ),
        ef => g1 => g2 => Lists.Bool.by(
          b => {Bool.or(b, Nat.is_lt(k, l)) == True{}: Bool} -> {
            Some{Lines.Entry.first(j, q, 0n)} == Some{Lines.Entry.first(i, r, 0n)}: Maybe<&2, Types.Entry>
          },
          Bool.and(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r)),
          +et2 => g3 => (
            %Ledgers.Id.is_eq_sound(j, i)(
              Shared.Bool.and_true_left(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r))(et2)
            ): {Some{Lines.Entry.first(j, q, 0n)} == Some{Lines.Entry.first(_, r, 0n)}: Maybe<&2, Types.Entry>}
            %Coded.Request.is_eq_sound(q, r)(
              Shared.Bool.and_true_right(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r))(et2)
            ): {Some{Lines.Entry.first(j, q, 0n)} == Some{Lines.Entry.first(j, _, 0n)}: Maybe<&2, Types.Entry>}
            {==}
          ),
          ef2 => g3 => Lists.Bool.clash(
            {Some{Lines.Entry.first(j, q, 0n)} == Some{Lines.Entry.first(i, r, 0n)}: Maybe<&2, Types.Entry>},
            Nat.is_lt(k, l),
            Shared.Nat.le_nlt(l, k)(Shared.Nat.lt_weak(l, k)(g1)),
            g3
          )
        )(g2)
      )(h1)(h2)

# First.kept, with the ask x a start that leads on the other side of d
def First.kept.of(
  +d: Delta,
  +s: Facts.Facts(),
  +f: Bool,
  +h: Hashes.Hash,
  +x: Types.Ask,
  +xin: {
    List.contains(
      ~Types.Ask,
      ~Coded.Ask.is_eq,
      Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
      x
    )
      == True{}: Bool
  },
  +xl: {Lines.Ask.leads(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h), x) == True{}: Bool}
) -> {
  Lines.Store.first(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h) == Lines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>
}:
  Lists.Maybe.by(
    Types.Ask,
    m => {Lines.Store.first.of(m) == Lines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>},
    Lists.List.pick(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~Lines.Ask.leads,
      Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
      Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h)
    ),
    en => Lists.Bool.clash(
      {None{} == Lines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>},
      Lines.Ask.leads(Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h), x),
      List.pick_miss(
        ~Types.Ask,
        ~List<&2, Types.Ask>,
        ~Lines.Ask.leads,
        ~Coded.Ask.is_eq,
        ~Coded.Ask.laws(),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
        x
      )(en)(xin),
      xl
    ),
    +y => +ey => Led.same(x, y)(
      Lists.List.holds_in(
        ~Types.Ask,
        ~Types.Ask,
        ~Lines.Ask.led,
        ~Coded.Ask.is_eq,
        ~Coded.Ask.laws(),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
        x,
        y
      )(xl)(
        Lists.List.pick_in(
          ~Types.Ask,
          ~List<&2, Types.Ask>,
          ~Lines.Ask.leads,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
          Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
          y
        )(ey)
      )
    )(
      Lists.List.holds_in(
        ~Types.Ask,
        ~Types.Ask,
        ~Lines.Ask.led,
        ~Coded.Ask.is_eq,
        ~Coded.Ask.laws(),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
        y,
        x
      )(
        Lists.List.pick_hit(
          ~Types.Ask,
          ~List<&2, Types.Ask>,
          ~Lines.Ask.leads,
          Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
          Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h),
          y
        )(ey)
      )(xin)
    )
  )

# the ask that gives version 0 of a store gives the version 0 that the store
# has on the other side of a d that starts no store
def First.kept(+d: Delta, +s: Facts.Facts(), +f: Bool, +h: Hashes.Hash, +x: Types.Ask) -> {
  Delta.ok(d) == True{}: Bool
} -> {
  Lists.List.pick(
    ~Types.Ask,
    ~List<&2, Types.Ask>,
    ~Lines.Ask.leads,
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
    Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h)
  )
    == Some{x}: Maybe<&2, Types.Ask>
} -> {
  Lines.Store.first(Facts.Facts.list(Delta.side(d, s, Bool.not(f))), h) == Lines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>
}:
  +ok => +e => First.kept.of(
    d,
    s,
    f,
    h,
    x,
    Starts.kept(d, s, f, h, x)(ok)(
      Lists.List.pick_in(
        ~Types.Ask,
        ~List<&2, Types.Ask>,
        ~Lines.Ask.leads,
        ~Coded.Ask.is_eq,
        ~Coded.Ask.laws(),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
        x
      )(e)
    ),
    Leads.kept(d, s, f, h, x)(ok)(
      Lists.List.pick_hit(
        ~Types.Ask,
        ~List<&2, Types.Ask>,
        ~Lines.Ask.leads,
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
        Lines.Starts.of(Facts.Facts.list(Delta.side(d, s, f)), h),
        x
      )(e)
    )
  )

# after the node adds a d that starts no store, version 0 of a store is as
# before
def First.same(+d: Delta, +s: Facts.Facts(), +h: Hashes.Hash) -> {Delta.ok(d) == True{}: Bool} -> {
  Lines.Store.first(Facts.Facts.list(Delta.to(d, s)), h) == Lines.Store.first(Facts.Facts.list(s), h): Maybe<&2, Types.Entry>
}:
  +ok => Lists.Maybe.by(
    Types.Ask,
    m => {
      Lines.Store.first(Facts.Facts.list(Delta.to(d, s)), h) == Lines.Store.first.of(m): Maybe<&2, Types.Entry>
    },
    Lists.List.pick(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~Lines.Ask.leads,
      Lines.Starts.of(Facts.Facts.list(s), h),
      Lines.Starts.of(Facts.Facts.list(s), h)
    ),
    +en => Lists.Maybe.by(
      Types.Ask,
      m => {Lines.Store.first.of(m) == None{}: Maybe<&2, Types.Entry>},
      Lists.List.pick(
        ~Types.Ask,
        ~List<&2, Types.Ask>,
        ~Lines.Ask.leads,
        Lines.Starts.of(Facts.Facts.list(Delta.to(d, s)), h),
        Lines.Starts.of(Facts.Facts.list(Delta.to(d, s)), h)
      ),
      en2 => {==},
      +y => ey => Equal.trans(
        Maybe<&2, Types.Entry>,
        Lines.Store.first.of(Some{y}),
        Lines.Store.first(Facts.Facts.list(s), h),
        None{},
        Equal.sym(
          Maybe<&2, Types.Entry>,
          Lines.Store.first(Facts.Facts.list(s), h),
          Lines.Store.first.of(Some{y}),
          First.kept(d, s, True{}, h, y)(ok)(ey)
        ),
        Equal.cong(
          Maybe<&2, Types.Ask>,
          Maybe<&2, Types.Entry>,
          m => Lines.Store.first.of(m),
          Lists.List.pick(
            ~Types.Ask,
            ~List<&2, Types.Ask>,
            ~Lines.Ask.leads,
            Lines.Starts.of(Facts.Facts.list(s), h),
            Lines.Starts.of(Facts.Facts.list(s), h)
          ),
          None{},
          en
        )
      )
    ),
    +x => ex => First.kept(d, s, False{}, h, x)(ok)(ex)
  )

# Lines that the new fact is no vote for
# --------------------------------------

# after the node adds d, the next slot of a line that d is no vote for a slot
# of gives what it gave, once the rule u of the slot is known
def Step.same.at(+d: Delta, +s: Facts.Facts(), +c: Ledgers.Line, +st: Lines.State, u: Maybe<&2, Lines.Rule>) -> {
  Delta.spares(d, c) == True{}: Bool
} -> {Lines.Line.step.at(Delta.to(d, s), c, st, u) == Lines.Line.step.at(s, c, st, u): Maybe<&2, Lines.State>}:
  match u:
    case None{}:
      h => {==}
    case Some{+rule}:
      h => Equal.cong(
        Maybe<&2, Types.Pick>,
        Maybe<&2, Lines.State>,
        m => Lines.Line.step.of(st, m),
        Lines.Votes.decided(Delta.to(d, s), Types.Step.At{c, Lines.State.slot(st)}, Lines.Rule.nodes(rule)),
        Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(st)}, Lines.Rule.nodes(rule)),
        Decided.same(d, s, c, Lines.State.slot(st), Lines.Rule.nodes(rule))(
          Delta.spares_keeps(d, c, Lines.State.slot(st))(h)
        )
      )

# after the node adds d, the next slot of a line that d is no vote for a slot
# of gives what it gave
def Step.same(
  +d: Delta,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State
) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Lines.Line.step(Delta.to(d, s), R, c, st) == Lines.Line.step(s, R, c, st): Maybe<&2, Lines.State>
}:
  h => Step.same.at(d, s, c, st, Lines.Line.rule(R, c, Lines.State.versions(st)))(h)

# after the node adds d, a run of a line that d is no vote for a slot of ends
# where it ended
def Run.same(
  fuel: Nat,
  +d: Delta,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State,
  m: Maybe<&2, Lines.State>
) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Lines.Line.run(fuel, Delta.to(d, s), R, c, st, m) == Lines.Line.run(fuel, s, R, c, st, m): Lines.State
}:
  match fuel m:
    case 0n _:
      h => {==}
    case 1n+f None{}:
      h => {==}
    case 1n+(+f) Some{+st2}:
      +h => (
        %Step.same(d, s, R, c, st2)(h): {
          Lines.Line.run(f, Delta.to(d, s), R, c, st2, Lines.Line.step(Delta.to(d, s), R, c, st2))
            == Lines.Line.run(f, s, R, c, st2, _): Lines.State
        }
        Run.same(f, d, s, R, c, st2, Lines.Line.step(Delta.to(d, s), R, c, st2))(h)
      )

# after the node adds d, a line that d is no vote for a slot of goes from a
# state as far as before
def Start.same(
  +d: Delta,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State
) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Lines.Line.start(Delta.to(d, s), R, c, st) == Lines.Line.start(s, R, c, st): Lines.State
}:
  +h => (
    %Bound.same(d, s, c)(h): {
      Lines.Line.start(Delta.to(d, s), R, c, st) == Lines.Line.run(_, s, R, c, st, Lines.Line.step(s, R, c, st)): Lines.State
    }
    %Step.same(d, s, R, c, st)(h): {
      Lines.Line.start(Delta.to(d, s), R, c, st)
        == Lines.Line.run(Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c), s, R, c, st, _): Lines.State
    }
    Run.same(
      Lines.Line.bound(Facts.Facts.list(Delta.to(d, s)), c),
      d,
      s,
      R,
      c,
      st,
      Lines.Line.step(Delta.to(d, s), R, c, st)
    )(h)
  )

# after the node adds d, a line that d is no vote for a slot of goes from its
# version 0 as far as before
def From.same(
  +d: Delta,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>
) -> {Delta.spares(d, c) == True{}: Bool} -> {
  Lines.Line.from(Delta.to(d, s), R, c, m) == Lines.Line.from(s, R, c, m): Maybe<&2, Lines.State>
}:
  match m:
    case None{}:
      h => {==}
    case Some{+e}:
      h => Equal.cong(
        Lines.State,
        Maybe<&2, Lines.State>,
        x => Some{x},
        Lines.Line.start(Delta.to(d, s), R, c, Lines.State{[e], 1n}),
        Lines.Line.start(s, R, c, Lines.State{[e], 1n}),
        Start.same(d, s, R, c, Lines.State{[e], 1n})(h)
      )

# after the node adds a d that starts no store and is no vote for a slot of
# the store of h, the state of that store is as before
def Store.same(+d: Delta, +s: Facts.Facts(), +h: Hashes.Hash) -> {Delta.ok(d) == True{}: Bool} -> {
  Delta.spares(d, Ledgers.Line{h, None{}}) == True{}: Bool
} -> {Lines.Store.state(Delta.to(d, s), h) == Lines.Store.state(s, h): Maybe<&2, Lines.State>}:
  ok => sp => (
    %First.same(d, s, h)(ok): {
      Lines.Store.state(Delta.to(d, s), h) == Lines.Line.from(s, None{}, Ledgers.Line{h, None{}}, _): Maybe<&2, Lines.State>
    }
    From.same(d, s, None{}, Ledgers.Line{h, None{}}, Lines.Store.first(Facts.Facts.list(Delta.to(d, s)), h))(sp)
  )

# after the node adds d, the state of a branch that d is no vote for a slot
# of is as before, once the versions m of its store are known
def Branch.same.at(+d: Delta, +s: Facts.Facts(), +c: Ledgers.Line, m: Maybe<&2, List<&2, Types.Entry>>) -> {
  Delta.spares(d, c) == True{}: Bool
} -> {Lines.Branch.state(Delta.to(d, s), c, m) == Lines.Branch.state(s, c, m): Maybe<&2, Lines.State>}:
  match m:
    case None{}:
      h => {==}
    case Some{+R}:
      h => From.same(d, s, Some{R}, c, Lines.Branch.first(R, c))(h)

# after the node adds a d that starts no store and is no vote for a slot of
# a branch or of its store, the state of the branch is as before
def Branch.same(+d: Delta, +s: Facts.Facts(), +h: Hashes.Hash, +b: String) -> {Delta.ok(d) == True{}: Bool} -> {
  Delta.spares(d, Ledgers.Line{h, None{}}) == True{}: Bool
} -> {Delta.spares(d, Ledgers.Line{h, Some{b}}) == True{}: Bool} -> {
  Lines.Line.state(Delta.to(d, s), Ledgers.Line{h, Some{b}}) == Lines.Line.state(s, Ledgers.Line{h, Some{b}}): Maybe<&2, Lines.State>
}:
  ok => sp => sb => (
    %Store.same(d, s, h)(ok)(sp): {
      Lines.Line.state(Delta.to(d, s), Ledgers.Line{h, Some{b}})
        == Lines.Branch.state(
          s,
          Ledgers.Line{h, Some{b}},
          Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, _)
        ): Maybe<&2, Lines.State>
    }
    Branch.same.at(d, s, Ledgers.Line{h, Some{b}}, Lines.Store.versions(Delta.to(d, s), h))(sb)
  )

# a node that takes in an ask that starts no store reads each line as before
def Line.state_asked(+name: String, +s: Facts.Facts(), +a: Types.Ask, +c: Ledgers.Line) -> {
  Facts.Request.is_start(Lines.Ask.request(a)) == False{}: Bool
} -> {
  Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c) == Lines.Line.state(s, c): Maybe<&2, Lines.State>
}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => Store.same(Delta.Ask{name, a}, s, h)(
        %Equal.sym(Bool, Facts.Request.is_start(Lines.Ask.request(a)), False{}, e): {Bool.not(_) == True{}: Bool}
        {==}
      )({==})
    case Ledgers.Line{+h, Some{+b}}:
      e => Branch.same(Delta.Ask{name, a}, s, h, b)(
        %Equal.sym(Bool, Facts.Request.is_start(Lines.Ask.request(a)), False{}, e): {Bool.not(_) == True{}: Bool}
        {==}
      )({==})({==})

# A vote of a node that decides alone
# -----------------------------------

# the facts s with the vote of the node name for the pick pk at the slot k of
# the line c
def Alone.to(+s: Facts.Facts(), name: String, c: Ledgers.Line, k: Nat, pk: Types.Pick) -> Facts.Facts():
  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk})

# a set that holds no vote of a node for a step holds no vote of it for a
# pick at that step
def Cast.none(+s: Facts.Facts(), +name: String, +st: Types.Step, +o: Types.Pick) -> {
  Facts.Facts.cast(s, name, st) == False{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{name, st, o}) == False{}: Bool}:
  nc => Lists.Bool.by(
    b => {b == False{}: Bool},
    Facts.Facts.has(s, Types.Fact.Vote{name, st, o}),
    et => Lists.Bool.clash(
      {True{} == False{}: Bool},
      Facts.Facts.cast(s, name, st),
      nc,
      Lists.List.in_some(
        ~Types.Fact,
        ~Facts.Seat,
        ~Facts.Fact.is_cast,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        Facts.Facts.list(s),
        Facts.Seat{name, st},
        Types.Fact.Vote{name, st, o}
      )(
        Equal.trans(
          Bool,
          List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{name, st, o}),
          Facts.Facts.has(s, Types.Fact.Vote{name, st, o}),
          True{},
          Equal.sym(
            Bool,
            Facts.Facts.has(s, Types.Fact.Vote{name, st, o}),
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{name, st, o}),
            Facts.Facts.has_list(s, Types.Fact.Vote{name, st, o})
          ),
          et
        )
      )(
        Shared.Bool.and_both(String.eq(name, name), Coded.Step.is_eq(st, st))(Texts.String.eq_refl(name))(
          Coded.Step.is_eq_refl(st)
        )
      )
    ),
    ef => {==}
  )

# a set with a fact holds it
def Added.has(+s: Facts.Facts(), +y: Types.Fact) -> {Facts.Facts.has(Facts.Facts.add(s, y), y) == True{}: Bool}:
  Equal.trans(
    Bool,
    Facts.Facts.has(Facts.Facts.add(s, y), y),
    Bool.or(Coded.Fact.is_eq(y, y), Facts.Facts.has(s, y)),
    True{},
    Facts.Facts.has_add(s, y, y),
    (
      %Equal.sym(Bool, Coded.Fact.is_eq(y, y), True{}, Coded.Fact.is_eq_refl(y)): {
        Bool.or(_, Facts.Facts.has(s, y)) == True{}: Bool
      }
      {==}
    )
  )

# after a node that held no vote for a step votes there, its one vote for a
# pick at that step is that vote
def Vote.only(+s: Facts.Facts(), +name: String, +st: Types.Step, +pk: Types.Pick, +o: Types.Pick) -> {
  Facts.Facts.cast(s, name, st) == False{}: Bool
} -> {
  Facts.Facts.has(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), Types.Fact.Vote{name, st, o}) == True{}: Bool
} -> {o == pk: Types.Pick}:
  nc => h => Shared.Maybe.some_inj(
    Types.Pick,
    o,
    pk,
    Equal.cong(
      Types.Fact,
      Maybe<&2, Types.Pick>,
      f => Fact.pick(f),
      Types.Fact.Vote{name, st, o},
      Types.Fact.Vote{name, st, pk},
      Coded.Fact.is_eq_sound(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk})(
        Equal.trans(
          Bool,
          Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk}),
          Bool.or(Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk}), False{}),
          True{},
          Shared.Bool.or_false(Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk})),
          (
            %Cast.none(s, name, st, o)(nc): {
              Bool.or(Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk}), _) == True{}: Bool
            }
            Equal.trans(
              Bool,
              Bool.or(
                Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk}),
                Facts.Facts.has(s, Types.Fact.Vote{name, st, o})
              ),
              Facts.Facts.has(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), Types.Fact.Vote{name, st, o}),
              True{},
              Equal.sym(
                Bool,
                Facts.Facts.has(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), Types.Fact.Vote{name, st, o}),
                Bool.or(
                  Coded.Fact.is_eq(Types.Fact.Vote{name, st, o}, Types.Fact.Vote{name, st, pk}),
                  Facts.Facts.has(s, Types.Fact.Vote{name, st, o})
                ),
                Facts.Facts.has_add(s, Types.Fact.Vote{name, st, pk}, Types.Fact.Vote{name, st, o})
              ),
              h
            )
          )
        )
      )
    )
  )

# after a node that held no vote for a step votes there, no pick stands
# against its pick, when the node decides alone
def Alone.beats(
  +s: Facts.Facts(),
  +name: String,
  +st: Types.Step,
  +pk: Types.Pick,
  +X: List<&2, Types.Pick>,
  +o: Types.Pick
) -> {Facts.Facts.cast(s, name, st) == False{}: Bool} -> {
  Lines.Rival.beats(
    Lines.Rival{Lines.Tally{Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name], X}, pk},
    o
  )
    == True{}: Bool
}:
  nc => Lists.Bool.by(
    b => {
      Bool.or(Coded.Pick.is_eq(o, pk), Bool.not(Lists.Nat.most(1n, Shared.Nat.add_if(b, 0n)))) == True{}: Bool
    },
    Facts.Facts.has(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), Types.Fact.Vote{name, st, o}),
    et => (
      %Vote.only(s, name, st, pk, o)(nc)(et): {
        Bool.or(Coded.Pick.is_eq(o, _), Bool.not(Lists.Nat.most(1n, 1n))) == True{}: Bool
      }
      %Equal.sym(Bool, Coded.Pick.is_eq(o, o), True{}, Coded.Pick.is_eq_refl(o)): {
        Bool.or(_, Bool.not(Lists.Nat.most(1n, 1n))) == True{}: Bool
      }
      {==}
    ),
    ef => Shared.Bool.or_true_right(Coded.Pick.is_eq(o, pk))
  )

# after a node that held no vote for a step votes there, no pick of ys stands
# against its pick, when the node decides alone
def Alone.holds(
  ys: List<&2, Types.Pick>,
  +s: Facts.Facts(),
  +name: String,
  +st: Types.Step,
  +pk: Types.Pick,
  +X: List<&2, Types.Pick>
) -> {Facts.Facts.cast(s, name, st) == False{}: Bool} -> {
  Shared.List.holds(
    ~Types.Pick,
    ~Lines.Rival,
    ~Lines.Rival.beats,
    ys,
    Lines.Rival{Lines.Tally{Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name], X}, pk}
  )
    == True{}: Bool
}:
  match ys:
    case Nil{}:
      nc => {==}
    case Con{+y, +r}:
      +nc => Shared.List.all.if_both(
        Lines.Rival.beats(
          Lines.Rival{Lines.Tally{Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name], X}, pk},
          y
        ),
        u => Shared.List.holds(
          ~Types.Pick,
          ~Lines.Rival,
          ~Lines.Rival.beats,
          r,
          Lines.Rival{Lines.Tally{Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name], X}, pk}
        )
      )(Alone.beats(s, name, st, pk, X, y)(nc))(Alone.holds(r, s, name, st, pk, X)(nc))

# after a node that held no vote for a step votes there, the node alone
# decided its pick for the step
def Alone.decided(+s: Facts.Facts(), +name: String, +st: Types.Step, +pk: Types.Pick) -> {
  Facts.Facts.cast(s, name, st) == False{}: Bool
} -> {
  Lines.Votes.decided(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name]) == Some{pk}: Maybe<&2, Types.Pick>
}:
  nc => Wins.decided(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, [name], pk)(
    Shared.Bool.and_both(
      Lines.Voting.most([name], Lines.Voting{Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), st, pk}),
      Shared.List.holds(
        ~Types.Pick,
        ~Lines.Rival,
        ~Lines.Rival.beats,
        Lines.Votes.picks(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk})), st),
        Lines.Rival{
          Lines.Tally{
            Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}),
            st,
            [name],
            Lines.Votes.picks(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk})), st)
          },
          pk
        }
      )
    )(
      %Equal.sym(
        Bool,
        Facts.Facts.has(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk}), Types.Fact.Vote{name, st, pk}),
        True{},
        Added.has(s, Types.Fact.Vote{name, st, pk})
      ): {Lists.Nat.most(1n, Shared.Nat.add_if(_, 0n)) == True{}: Bool}
      {==}
    )(
      Alone.holds(
        Lines.Votes.picks(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk})), st),
        s,
        name,
        st,
        pk,
        Lines.Votes.picks(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, st, pk})), st)
      )(nc)
    )
  )

# after a node that alone decides the slot k of a line, and held no vote
# there, votes there for a pick whose id made no version, the slot makes the
# next version: that pick
def Alone.step(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>
) -> {Lines.Line.rule(R, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {
  Lines.Line.step(Alone.to(s, name, c, k, pk), R, c, Lines.State{vs, k})
    == Some{Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}}: Maybe<&2, Lines.State>
}:
  er => ed => nc => (
    %Equal.sym(Maybe<&2, Lines.Rule>, Lines.Line.rule(R, c, vs), Some{Lines.Rule{g, [name]}}, er): {
      Lines.Line.step.at(Alone.to(s, name, c, k, pk), c, Lines.State{vs, k}, _)
        == Some{Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}}: Maybe<&2, Lines.State>
    }
    %Equal.sym(
      Maybe<&2, Types.Pick>,
      Lines.Votes.decided(Alone.to(s, name, c, k, pk), Types.Step.At{c, k}, [name]),
      Some{pk},
      Alone.decided(s, name, Types.Step.At{c, k}, pk)(nc)
    ): {
      Lines.Line.step.of(Lines.State{vs, k}, _)
        == Some{Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}}: Maybe<&2, Lines.State>
    }
    %Equal.sym(
      Bool,
      Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)),
      False{},
      ed
    ): {
      Some{Lines.State.put.if(vs, k, pk, _)}
        == Some{Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}}: Maybe<&2, Lines.State>
    }
    {==}
  )

# the state b comes after a decided slot of the state a: its versions extend
# those of a, and its slot is the next one
def Step.Next(a: Lines.State, b: Lines.State) -> Type:
  Lists.List.Ext(Types.Entry, Lines.State.versions(a), Lines.State.versions(b))
    & {Lines.State.slot(b) == 1n+Lines.State.slot(a): Nat}

# the state after a decided slot comes after the state before it, whether the
# pick is a new version or not (dup)
def Step.next.if(+vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick, dup: Bool) -> Step.Next(
  Lines.State{vs, k},
  Lines.State.put.if(vs, k, pk, dup)
):
  match dup:
    case True{}:
      (Lists.List.ext_refl(Types.Entry, vs), {==})
    case False{}:
      (Lists.List.ext_snoc(Types.Entry, vs, Types.Entry{pk, k}), {==})

# Step.next, once the decided pick m of the slot is known
def Step.next.of(st: Lines.State, -st2: Lines.State, m: Maybe<&2, Types.Pick>) -> {
  Lines.Line.step.of(st, m) == Some{st2}: Maybe<&2, Lines.State>
} -> Step.Next(st, st2):
  match st m:
    case Lines.State{+vs, +k} None{}:
      e => Empty.absurd(Step.Next(Lines.State{vs, k}, st2), Shared.Maybe.none_ne_some(Lines.State, st2, e))
    case Lines.State{+vs, +k} Some{+pk}:
      e => (
        %Shared.Maybe.some_inj(Lines.State, Lines.State.put(vs, k, pk), st2, e): Step.Next(Lines.State{vs, k}, _)
        Step.next.if(vs, k, pk, Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)))
      )

# Step.next, once the rule u of the slot is known
def Step.next.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +st: Lines.State,
  -st2: Lines.State,
  u: Maybe<&2, Lines.Rule>
) -> {Lines.Line.step.at(s, c, st, u) == Some{st2}: Maybe<&2, Lines.State>} -> Step.Next(st, st2):
  match u:
    case None{}:
      e => Empty.absurd(Step.Next(st, st2), Shared.Maybe.none_ne_some(Lines.State, st2, e))
    case Some{rule}:
      e => Step.next.of(
        st,
        st2,
        Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(st)}, Lines.Rule.nodes(rule))
      )(e)

# the state after a decided slot comes after the state before it
def Step.next(
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State,
  -st2: Lines.State
) -> {Lines.Line.step(s, R, c, st) == Some{st2}: Maybe<&2, Lines.State>} -> Step.Next(st, st2):
  e => Step.next.at(s, c, st, st2, Lines.Line.rule(R, c, Lines.State.versions(st)))(e)

# the versions of a state that comes after a extend those of a
def Next.ext(-a: Lines.State, -b: Lines.State, n: Step.Next(a, b)) -> Lists.List.Ext(
  Types.Entry,
  Lines.State.versions(a),
  Lines.State.versions(b)
):
  (x, e) = n
  x

# the slot of a state that comes after a is the slot after that of a
def Next.slot(-a: Lines.State, -b: Lines.State, n: Step.Next(a, b)) -> {
  Lines.State.slot(b) == 1n+Lines.State.slot(a): Nat
}:
  (x, e) = n
  e

# the versions after a run extend the versions before it
def Run.grows(
  f: Nat,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State
) -> Lists.List.Ext(
  Types.Entry,
  Lines.State.versions(st),
  Lines.State.versions(Lines.Line.run(f, s, R, c, st, Lines.Line.step(s, R, c, st)))
):
  match f:
    case 0n:
      Lists.List.ext_refl(Types.Entry, Lines.State.versions(st))
    case 1n+(+p):
      Lists.Maybe.by(
        Lines.State,
        m => Lists.List.Ext(
          Types.Entry,
          Lines.State.versions(st),
          Lines.State.versions(Lines.Line.run(1n+p, s, R, c, st, m))
        ),
        Lines.Line.step(s, R, c, st),
        en => Lists.List.ext_refl(Types.Entry, Lines.State.versions(st)),
        +st2 => e2 => Lists.List.ext_trans(
          Types.Entry,
          Lines.State.versions(st),
          Lines.State.versions(st2),
          Lines.State.versions(Lines.Line.run(p, s, R, c, st2, Lines.Line.step(s, R, c, st2)))
        )(Next.ext(st, st2, Step.next(s, R, c, st, st2)(e2)))(Run.grows(p, s, R, c, st2))
      )

# the slot after a run is no less than the slot before it
def Run.slot_le(
  f: Nat,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State
) -> {
  Nat.is_le(
    Lines.State.slot(st),
    Lines.State.slot(Lines.Line.run(f, s, R, c, st, Lines.Line.step(s, R, c, st)))
  )
    == True{}: Bool
}:
  match f:
    case 0n:
      Shared.Nat.le_refl(Lines.State.slot(st))
    case 1n+(+p):
      Lists.Maybe.by(
        Lines.State,
        m => {
          Nat.is_le(Lines.State.slot(st), Lines.State.slot(Lines.Line.run(1n+p, s, R, c, st, m))) == True{}: Bool
        },
        Lines.Line.step(s, R, c, st),
        en => Shared.Nat.le_refl(Lines.State.slot(st)),
        +st2 => e2 => Shared.Nat.le_trans(
          Lines.State.slot(st),
          Lines.State.slot(st2),
          Lines.State.slot(Lines.Line.run(p, s, R, c, st2, Lines.Line.step(s, R, c, st2)))
        )(
          %Equal.sym(
            Nat,
            Lines.State.slot(st2),
            1n+Lines.State.slot(st),
            Next.slot(st, st2, Step.next(s, R, c, st, st2)(e2))
          ): {Nat.is_le(Lines.State.slot(st), _) == True{}: Bool}
          Shared.Nat.le_succ(Lines.State.slot(st), Lines.State.slot(st))(Shared.Nat.le_refl(Lines.State.slot(st)))
        )(Run.slot_le(p, s, R, c, st2))
      )

# after the node adds d, a slot that d is no vote for gives what it gave,
# once the rule u of the slot is known
def Step.kept.at(+d: Delta, +s: Facts.Facts(), +c: Ledgers.Line, +st: Lines.State, u: Maybe<&2, Lines.Rule>) -> {
  Delta.keeps(d, c, Lines.State.slot(st)) == True{}: Bool
} -> {Lines.Line.step.at(Delta.to(d, s), c, st, u) == Lines.Line.step.at(s, c, st, u): Maybe<&2, Lines.State>}:
  match u:
    case None{}:
      h => {==}
    case Some{+rule}:
      h => Equal.cong(
        Maybe<&2, Types.Pick>,
        Maybe<&2, Lines.State>,
        m => Lines.Line.step.of(st, m),
        Lines.Votes.decided(Delta.to(d, s), Types.Step.At{c, Lines.State.slot(st)}, Lines.Rule.nodes(rule)),
        Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(st)}, Lines.Rule.nodes(rule)),
        Decided.same(d, s, c, Lines.State.slot(st), Lines.Rule.nodes(rule))(h)
      )

# a number below another is not it
def Nat.lt_ne(+a: Nat, +b: Nat) -> {Nat.is_le(1n+a, b) == True{}: Bool} -> {Nat.is_eq(a, b) == False{}: Bool}:
  lt => Lists.Bool.by(
    x => {x == False{}: Bool},
    Nat.is_eq(a, b),
    et => Lists.Bool.clash(
      {True{} == False{}: Bool},
      Nat.is_le(1n+a, a),
      Shared.Nat.succ_nle(a),
      (
        %Equal.sym(Nat, a, b, Shared.Nat.is_eq_sound(a, b)(et)): {Nat.is_le(1n+a, _) == True{}: Bool}
        lt
      )
    ),
    ef => {==}
  )

# a vote for the slot k of the line c is no vote for a slot of c below k
def Alone.keeps(+name: String, +c: Ledgers.Line, +k: Nat, +pk: Types.Pick, +j: Nat) -> {
  Nat.is_le(1n+j, k) == True{}: Bool
} -> {Delta.keeps(Delta.Vote{name, c, k, pk}, c, j) == True{}: Bool}:
  lt => (
    %Equal.sym(Bool, Nat.is_eq(j, k), False{}, Nat.lt_ne(j, k)(lt)): {
      Bool.not(Bool.and(Ledgers.Line.is_eq(c, c), _)) == True{}: Bool
    }
    %Equal.sym(
      Bool,
      Bool.and(Ledgers.Line.is_eq(c, c), False{}),
      False{},
      Shared.Bool.and_false_right(Ledgers.Line.is_eq(c, c))
    ): {Bool.not(_) == True{}: Bool}
    {==}
  )

# a run of f2 slots from the state st, after the node votes, gives the pick
# pk of the slot k as the version after the versions vs
def Alone.Got(
  s: Facts.Facts(),
  name: String,
  c: Ledgers.Line,
  vs: List<&2, Types.Entry>,
  k: Nat,
  pk: Types.Pick,
  R: Maybe<&2, List<&2, Types.Entry>>,
  f2: Nat,
  st: Lines.State
) -> Type:
  {
    List.get(
      &2,
      Types.Entry,
      Lines.State.versions(
        Lines.Line.run(
          f2,
          Alone.to(s, name, c, k, pk),
          R,
          c,
          st,
          Lines.Line.step(Alone.to(s, name, c, k, pk), R, c, st)
        )
      ),
      List.length(&2, Types.Entry, vs)
    )
      == Some{Types.Entry{pk, k}}: Maybe<&2, Types.Entry>
  }

# from the state that the line was read up to, a run after the vote makes the
# pick the next version, when it has a slot to go
def Alone.end(
  f2: Nat,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>
) -> {Lines.Line.rule(R, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {
  Nat.is_lt(k, Nat.add(f2, k)) == True{}: Bool
} -> Alone.Got(s, name, c, vs, k, pk, R, f2, Lines.State{vs, k}):
  match f2:
    case 0n:
      er => ed => nc => hl => Lists.Bool.clash(
        Alone.Got(s, name, c, vs, k, pk, R, 0n, Lines.State{vs, k}),
        Nat.is_lt(k, k),
        Shared.Nat.lt_irrefl(k),
        hl
      )
    case 1n+(+p):
      er => ed => nc => hl => (
        %Equal.sym(
          Maybe<&2, Lines.State>,
          Lines.Line.step(Alone.to(s, name, c, k, pk), R, c, Lines.State{vs, k}),
          Some{Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}},
          Alone.step(s, name, c, vs, k, g, pk, R)(er)(ed)(nc)
        ): {
          List.get(
            &2,
            Types.Entry,
            Lines.State.versions(
              Lines.Line.run(1n+p, Alone.to(s, name, c, k, pk), R, c, Lines.State{vs, k}, _)
            ),
            List.length(&2, Types.Entry, vs)
          )
            == Some{Types.Entry{pk, k}}: Maybe<&2, Types.Entry>
        }
        Lists.List.ext_get(
          Types.Entry,
          List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]),
          Lines.State.versions(
            Lines.Line.run(
              p,
              Alone.to(s, name, c, k, pk),
              R,
              c,
              Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k},
              Lines.Line.step(
                Alone.to(s, name, c, k, pk),
                R,
                c,
                Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}
              )
            )
          ),
          List.length(&2, Types.Entry, vs),
          Types.Entry{pk, k}
        )(
          Run.grows(
            p,
            Alone.to(s, name, c, k, pk),
            R,
            c,
            Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}
          )
        )(Lists.List.get_snoc(Types.Entry, vs, Types.Entry{pk, k}))
      )

# Alone.end, from a state that is the state that the line was read up to
def Alone.stop(
  +f2: Nat,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +st: Lines.State
) -> {Lines.Line.rule(R, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {st == Lines.State{vs, k}: Lines.State} -> {
  Nat.is_lt(k, Nat.add(f2, Lines.State.slot(st))) == True{}: Bool
} -> Alone.Got(s, name, c, vs, k, pk, R, f2, st):
  er => ed => nc => e => (
    %Equal.sym(Lines.State, st, Lines.State{vs, k}, e): (
      {
        Nat.is_lt(k, Nat.add(f2, Lines.State.slot(_))) == True{}: Bool
      } -> Alone.Got(s, name, c, vs, k, pk, R, f2, _)
    )
    Alone.end(f2, s, name, c, vs, k, g, pk, R)(er)(ed)(nc)
  )

# from a state whose slot is below k and decided, a run after the vote does
# what a run from the state after that slot does (ih)
def Alone.go(
  f2: Nat,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +st: Lines.State,
  +st2: Lines.State,
  +e2: {Lines.Line.step(s, R, c, st) == Some{st2}: Maybe<&2, Lines.State>},
  lt: {Nat.is_le(1n+Lines.State.slot(st), k) == True{}: Bool},
  ih: @f3: Nat -> {Nat.is_lt(k, Nat.add(f3, Lines.State.slot(st2))) == True{}: Bool} -> Alone.Got(
    s,
    name,
    c,
    vs,
    k,
    pk,
    R,
    f3,
    st2
  )
) -> {Nat.is_lt(k, Nat.add(f2, Lines.State.slot(st))) == True{}: Bool} -> Alone.Got(s, name, c, vs, k, pk, R, f2, st):
  match f2:
    case 0n:
      hl => Lists.Bool.clash(
        Alone.Got(s, name, c, vs, k, pk, R, 0n, st),
        Nat.is_lt(k, Lines.State.slot(st)),
        Shared.Nat.le_nlt(Lines.State.slot(st), k)(
          Shared.Nat.le_trans(Lines.State.slot(st), 1n+Lines.State.slot(st), k)(
            Shared.Nat.le_succ(Lines.State.slot(st), Lines.State.slot(st))(Shared.Nat.le_refl(Lines.State.slot(st)))
          )(lt)
        ),
        hl
      )
    case 1n+(+p):
      hl => (
        %Equal.sym(
          Maybe<&2, Lines.State>,
          Lines.Line.step(Alone.to(s, name, c, k, pk), R, c, st),
          Some{st2},
          Equal.trans(
            Maybe<&2, Lines.State>,
            Lines.Line.step(Alone.to(s, name, c, k, pk), R, c, st),
            Lines.Line.step(s, R, c, st),
            Some{st2},
            Step.kept.at(Delta.Vote{name, c, k, pk}, s, c, st, Lines.Line.rule(R, c, Lines.State.versions(st)))(
              Alone.keeps(name, c, k, pk, Lines.State.slot(st))(lt)
            ),
            e2
          )
        ): {
          List.get(
            &2,
            Types.Entry,
            Lines.State.versions(Lines.Line.run(1n+p, Alone.to(s, name, c, k, pk), R, c, st, _)),
            List.length(&2, Types.Entry, vs)
          )
            == Some{Types.Entry{pk, k}}: Maybe<&2, Types.Entry>
        }
        ih(p)(
          %Equal.sym(
            Nat,
            Lines.State.slot(st2),
            1n+Lines.State.slot(st),
            Next.slot(st, st2, Step.next(s, R, c, st, st2)(e2))
          ): {Nat.is_lt(k, Nat.add(p, _)) == True{}: Bool}
          %Equal.sym(
            Nat,
            Nat.add(p, 1n+Lines.State.slot(st)),
            1n+Nat.add(p, Lines.State.slot(st)),
            Shared.Nat.add_succ(p, Lines.State.slot(st))
          ): {Nat.is_lt(k, _) == True{}: Bool}
          hl
        )
      )

# when a run of f slots from the state st ends where the line was read up to,
# a run of f2 slots after the vote, with a slot to go beyond k, makes the pick
# the next version
def Alone.run(
  f: Nat,
  +f2: Nat,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +st: Lines.State
) -> {Lines.Line.rule(R, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {
  Lines.Line.run(f, s, R, c, st, Lines.Line.step(s, R, c, st)) == Lines.State{vs, k}: Lines.State
} -> {Nat.is_lt(k, Nat.add(f2, Lines.State.slot(st))) == True{}: Bool} -> Alone.Got(s, name, c, vs, k, pk, R, f2, st):
  match f:
    case 0n:
      er => ed => nc => e => hl => Alone.stop(f2, s, name, c, vs, k, g, pk, R, st)(er)(ed)(nc)(e)(hl)
    case 1n+(+p):
      +er => +ed => +nc => e => hl => Lists.Maybe.by(
        Lines.State,
        m => {Lines.Line.run(1n+p, s, R, c, st, m) == Lines.State{vs, k}: Lines.State} -> {
          Nat.is_lt(k, Nat.add(f2, Lines.State.slot(st))) == True{}: Bool
        } -> Alone.Got(s, name, c, vs, k, pk, R, f2, st),
        Lines.Line.step(s, R, c, st),
        en => e1 => hl1 => Alone.stop(f2, s, name, c, vs, k, g, pk, R, st)(er)(ed)(nc)(e1)(hl1),
        +st2 => +e2 => +e1 => hl1 => Alone.go(
          f2,
          s,
          name,
          c,
          vs,
          k,
          pk,
          R,
          st,
          st2,
          e2,
          (
            %Next.slot(st, st2, Step.next(s, R, c, st, st2)(e2)): {Nat.is_le(_, k) == True{}: Bool}
            %e1: {Nat.is_le(Lines.State.slot(st2), Lines.State.slot(_)) == True{}: Bool}
            Run.slot_le(p, s, R, c, st2)
          ),
          +f3 => h3 => Alone.run(p, f3, s, name, c, vs, k, g, pk, R, st2)(er)(ed)(nc)(e1)(h3)
        )(hl1)
      )(e)(hl)

# a store is not a branch of it
def Line.root_ne(+h: Hashes.Hash, +b: String) -> {
  Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}) == False{}: Bool
}:
  Lists.Bool.by(
    x => {x == False{}: Bool},
    Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}),
    et => Equal.cong(
      Ledgers.Line,
      Bool,
      l => Lines.Line.is_root(l),
      Ledgers.Line{h, None{}},
      Ledgers.Line{h, Some{b}},
      Ledgers.Line.is_eq_sound(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}})(et)
    ),
    ef => {==}
  )

# after the vote, a read of the line may go one slot beyond the slot k
def Alone.fuel(+s: Facts.Facts(), +name: String, +c: Ledgers.Line, +k: Nat, +pk: Types.Pick) -> {
  Nat.is_lt(k, Nat.add(Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c), 1n)) == True{}: Bool
}:
  Shared.Nat.lt_le(
    k,
    Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c),
    Nat.add(Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c), 1n)
  )(
    Shared.Nat.lt_le(k, 1n+k, Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c))(
      Shared.Nat.lt_succ(k)
    )(
      Bound.ge(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c, name, k, pk)(
        Equal.trans(
          Bool,
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Facts.Facts.list(Alone.to(s, name, c, k, pk)),
            Types.Fact.Vote{name, Types.Step.At{c, k}, pk}
          ),
          Facts.Facts.has(Alone.to(s, name, c, k, pk), Types.Fact.Vote{name, Types.Step.At{c, k}, pk}),
          True{},
          Equal.sym(
            Bool,
            Facts.Facts.has(Alone.to(s, name, c, k, pk), Types.Fact.Vote{name, Types.Step.At{c, k}, pk}),
            List.contains(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Facts.Facts.list(Alone.to(s, name, c, k, pk)),
              Types.Fact.Vote{name, Types.Step.At{c, k}, pk}
            ),
            Facts.Facts.has_list(Alone.to(s, name, c, k, pk), Types.Fact.Vote{name, Types.Step.At{c, k}, pk})
          ),
          Added.has(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk})
        )
      )
    )
  )(Shared.Nat.le_add_first(Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c), 1n))

# the state x has versions, and the version after the versions vs is the
# pick pk of the slot k
def Alone.Made(vs: List<&2, Types.Entry>, k: Nat, pk: Types.Pick, x: Maybe<&2, Lines.State>) -> Type:
  Exists(
    List<&2, Types.Entry>,
    vs2 => {
      Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, x) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & {
        List.get(&2, Types.Entry, vs2, List.length(&2, Types.Entry, vs)) == Some{Types.Entry{pk, k}}: Maybe<&2, Types.Entry>
      }
  )

# Line.voted_alone, for a line that goes from the version 0 m, with the
# versions R of its store
def Alone.from(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  +R: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, Types.Entry>
) -> {Lines.Line.rule(R, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {
  Lines.Line.from(s, R, c, m) == Some{Lines.State{vs, k}}: Maybe<&2, Lines.State>
} -> Alone.Made(vs, k, pk, Lines.Line.from(Alone.to(s, name, c, k, pk), R, c, m)):
  match m:
    case None{}:
      er => ed => nc => e => Empty.absurd(
        Alone.Made(vs, k, pk, None{}),
        Shared.Maybe.none_ne_some(Lines.State, Lines.State{vs, k}, e)
      )
    case Some{+e0}:
      er => ed => nc => e => (
        Lines.State.versions(Lines.Line.start(Alone.to(s, name, c, k, pk), R, c, Lines.State{[e0], 1n})),
        (
          {==},
          Alone.run(
            Lines.Line.bound(Facts.Facts.list(s), c),
            Lines.Line.bound(Facts.Facts.list(Alone.to(s, name, c, k, pk)), c),
            s,
            name,
            c,
            vs,
            k,
            g,
            pk,
            R,
            Lines.State{[e0], 1n}
          )(er)(ed)(nc)(
            Shared.Maybe.some_inj(
              Lines.State,
              Lines.Line.start(s, R, c, Lines.State{[e0], 1n}),
              Lines.State{vs, k},
              e
            )
          )(Alone.fuel(s, name, c, k, pk))
        )
      )

# Line.voted_alone, for a branch, once the versions m of its store are known
def Alone.branch(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {Lines.Rule.after.of(c, vs, m) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> {
  Lines.Branch.state(s, c, m) == Some{Lines.State{vs, k}}: Maybe<&2, Lines.State>
} -> Alone.Made(vs, k, pk, Lines.Branch.state(Alone.to(s, name, c, k, pk), c, m)):
  match m:
    case None{}:
      er => ed => nc => e => Empty.absurd(
        Alone.Made(vs, k, pk, None{}),
        Shared.Maybe.none_ne_some(Lines.State, Lines.State{vs, k}, e)
      )
    case Some{+R}:
      er => ed => nc => e => Alone.from(s, name, c, vs, k, g, pk, Some{R}, Lines.Branch.first(R, c))(er)(ed)(nc)(e)

# a node that alone decides the next slot of a line, and votes there for a
# pick whose id made no version of the line, makes the next version: that
# pick, when it held no vote of its own for the slot
def Line.voted_alone(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +pk: Types.Pick
) -> {Lines.Line.state(s, c) == Some{Lines.State{vs, k}}: Maybe<&2, Lines.State>} -> {
  Lines.Rule.after(s, c, vs) == Some{Lines.Rule{g, [name]}}: Maybe<&2, Lines.Rule>
} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)) == False{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k}, pk}), c)
      == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {
      List.get(&2, Types.Entry, vs2, List.length(&2, Types.Entry, vs)) == Some{Types.Entry{pk, k}}: Maybe<&2, Types.Entry>
    }
):
  match c:
    case Ledgers.Line{+h, None{}}:
      es => er => ed => nc => (
        %Equal.sym(
          Maybe<&2, Types.Entry>,
          Lines.Store.first(Facts.Facts.list(Alone.to(s, name, Ledgers.Line{h, None{}}, k, pk)), h),
          Lines.Store.first(Facts.Facts.list(s), h),
          First.same(Delta.Vote{name, Ledgers.Line{h, None{}}, k, pk}, s, h)({==})
        ): Alone.Made(
          vs,
          k,
          pk,
          Lines.Line.from(Alone.to(s, name, Ledgers.Line{h, None{}}, k, pk), None{}, Ledgers.Line{h, None{}}, _)
        )
        Alone.from(
          s,
          name,
          Ledgers.Line{h, None{}},
          vs,
          k,
          g,
          pk,
          None{},
          Lines.Store.first(Facts.Facts.list(s), h)
        )(er)(ed)(nc)(es)
      )
    case Ledgers.Line{+h, Some{+b}}:
      es => er => ed => nc => (
        %Equal.sym(
          Maybe<&2, Lines.State>,
          Lines.Store.state(Alone.to(s, name, Ledgers.Line{h, Some{b}}, k, pk), h),
          Lines.Store.state(s, h),
          Store.same(Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, pk}, s, h)({==})(
            %Equal.sym(
              Bool,
              Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}),
              False{},
              Line.root_ne(h, b)
            ): {Bool.not(_) == True{}: Bool}
            {==}
          )
        ): Alone.Made(
          vs,
          k,
          pk,
          Lines.Branch.state(
            Alone.to(s, name, Ledgers.Line{h, Some{b}}, k, pk),
            Ledgers.Line{h, Some{b}},
            Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, _)
          )
        )
        Alone.branch(s, name, Ledgers.Line{h, Some{b}}, vs, k, g, pk, Lines.Store.versions(s, h))(er)(ed)(nc)(es)
      )
