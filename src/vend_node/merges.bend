import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./content.bend as Contents
import ./reads.bend as Reads
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as Files
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./shared/files.bend as FileLaws
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Near files: laws
# ----------------
# Files x are near files y at the paths ps when they hold the same at each
# other path (RContents.Near.files). A merge reads only the paths where what
# it takes may differ from its base (RContents.Merge.few). Here: that
# nearness gives a read of a path, it holds for files and themselves, after
# a write, and from point to point, and the merge of the paths where theirs
# is near the base is the merge of every path (Few.files).

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# one of the paths qs is among ps, or x and y hold the same at it, when they
# hold the same at each of qs that is none of ps
def Near.go_at(
  +x: Files.Files(),
  +y: Files.Files(),
  +ps: List<&2, String>,
  qs: List<&2, String>,
  +q: String
) -> {
  RContents.Near.files.go(x, y, ps, qs) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, qs, q) == True{}: Bool
} -> {
  Bool.or(
    List.contains(~String, ~String.eq, ps, q),
    Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      h => hq => Empty.absurd(
        {
          Bool.or(
            List.contains(~String, ~String.eq, ps, q),
            Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(hq)
      )
    case Con{+r, +rest}:
      +h => hq => Lists.Bool.by(
        b => {
          List.any.if(u => List.contains(~String, ~String.eq, rest, q), b) == True{}: Bool
        } -> {
          Bool.or(
            List.contains(~String, ~String.eq, ps, q),
            Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))
          )
            == True{}: Bool
        },
        String.eq(r, q),
        e => hq2 => (
          %Texts.String.eq_sound(r, q)(e): {Bool.or(List.contains(~String, ~String.eq, ps, _), Formats.Content.same(Files.Files.get(x, _), Files.Files.get(y, _))) == True{}: Bool}
          Shared.Bool.and_true_left(Bool.or(List.contains(~String, ~String.eq, ps, r), Formats.Content.same(Files.Files.get(x, r), Files.Files.get(y, r))), RContents.Near.files.go(x, y, ps, rest))(h)),
        e => hq2 => Near.go_at(
          x,
          y,
          ps,
          rest,
          q
        )(
          Shared.Bool.and_true_right(
            Bool.or(
              List.contains(~String, ~String.eq, ps, r),
              Formats.Content.same(Files.Files.get(x, r), Files.Files.get(y, r))
            ),
            RContents.Near.files.go(x, y, ps, rest)
          )(h)
        )(hq2)
      )(hq)

# files near other files hold what they hold at a path of either that is
# none of the paths where they may differ
def Near.in(
  +x: Files.Files(),
  +y: Files.Files(),
  +ps: List<&2, String>,
  +q: String
) -> {
  RContents.Near.files(x, y, ps) == True{}: Bool
} -> {
  List.contains(
    ~String,
    ~String.eq,
    List.append(&2, String, Files.Files.paths(x), Files.Files.paths(y)),
    q
  )
    == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, ps, q) == False{}: Bool
} -> {Files.Files.get(x, q) == Files.Files.get(y, q): Maybe<&2, List<&2, U32>>}:
  hn => hm => hc => Formats.Content.same_sound(Files.Files.get(x, q), Files.Files.get(y, q))(
    %hc: {Bool.or(_, Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))) == True{}: Bool}
    Near.go_at(x, y, ps, List.append(&2, String, Files.Files.paths(x), Files.Files.paths(y)), q)(hn)(hm))

# files near other files hold what they hold at a path that is none of the
# paths where they may differ
def Near.out(
  +x: Files.Files(),
  +y: Files.Files(),
  +ps: List<&2, String>,
  +q: String
) -> {
  FileLaws.Files.wf(x) == True{}: Bool
} -> {
  FileLaws.Files.wf(y) == True{}: Bool
} -> {
  RContents.Near.files(x, y, ps) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, ps, q) == False{}: Bool
} -> {Files.Files.get(x, q) == Files.Files.get(y, q): Maybe<&2, List<&2, U32>>}:
  +wx => +wy => +hn => +hc => Lists.Maybe.by(
    List<&2, U32>,
    m => {Files.Files.get(x, q) == Files.Files.get(y, q): Maybe<&2, List<&2, U32>>},
    Files.Files.get(x, q),
    en => Lists.Maybe.by(
      List<&2, U32>,
      m => {Files.Files.get(x, q) == Files.Files.get(y, q): Maybe<&2, List<&2, U32>>},
      Files.Files.get(y, q),
      en2 => Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(x, q),
        None{},
        Files.Files.get(y, q),
        en,
        Equal.sym(Maybe<&2, List<&2, U32>>, Files.Files.get(y, q), None{}, en2)
      ),
      +ws => es => Near.in(
        x,
        y,
        ps,
        q
      )(
        hn
      )(
        Shared.List.contains_right(
          ~String,
          ~String.eq,
          Files.Files.paths(x),
          Files.Files.paths(y),
          q,
          FileLaws.Files.get_paths(y, q, ws)(wy)(es)
        )
      )(hc)
    ),
    +ws => es => Near.in(
      x,
      y,
      ps,
      q
    )(
      hn
    )(
      Shared.List.contains_left(
        ~String,
        ~String.eq,
        Files.Files.paths(x),
        Files.Files.paths(y),
        q,
        FileLaws.Files.get_paths(x, q, ws)(wx)(es)
      )
    )(hc)
  )

# the paths ps hold q, or x and y hold the same at q, when they hold the
# same at q unless ps holds it
def Near.at(
  +x: Files.Files(),
  +y: Files.Files(),
  +ps: List<&2, String>,
  +q: String,
  h: {
    List.contains(~String, ~String.eq, ps, q) == False{}: Bool
  } -> {Files.Files.get(x, q) == Files.Files.get(y, q): Maybe<&2, List<&2, U32>>}
) -> {
  Bool.or(
    List.contains(~String, ~String.eq, ps, q),
    Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))
  )
    == True{}: Bool
}:
  Lists.Bool.by(
    b => {
      Bool.or(b, Formats.Content.same(Files.Files.get(x, q), Files.Files.get(y, q))) == True{}: Bool
    },
    List.contains(~String, ~String.eq, ps, q),
    e => {==},
    e => (
      %h(e): {Formats.Content.same(Files.Files.get(x, q), _) == True{}: Bool}
      Formats.Content.same_refl(Files.Files.get(x, q)))
  )

# files hold what they hold at each of the paths qs
def Near.refl.go(
  +x: Files.Files(),
  +ps: List<&2, String>,
  qs: List<&2, String>
) -> {RContents.Near.files.go(x, x, ps, qs) == True{}: Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      %Equal.sym(
        Bool,
        Bool.or(
          List.contains(String, String.eq, ps, head),
          Formats.Content.same(Files.Files.get(x, head), Files.Files.get(x, head))
        ),
        True{},
        Near.at(x, x, ps, head, x1 => {==})
      ):
        {Bool.and(_, RContents.Near.files.go(x, x, ps, tail)) == True{}: Bool}
      Near.refl.go(x, ps, tail)

# files are near themselves
def Near.refl(
  +x: Files.Files(),
  +ps: List<&2, String>
) -> {RContents.Near.files(x, x, ps) == True{}: Bool}:
  %Equal.sym(
    Bool,
    RContents.Near.files.go(
      x,
      x,
      ps,
      List.append(&2, String, Files.Files.paths(x), Files.Files.paths(x))
    ),
    True{},
    Near.refl.go(x, ps, List.append(&2, String, Files.Files.paths(x), Files.Files.paths(x)))
  ):
    {_ == True{}: Bool}
  {==}

# the left side of an or that is false is false
def Or.false_left(a: Bool, b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {a == False{}: Bool}:
  match a:
    case False{}:
      x => {==}
    case True{}:
      x => x

# the right side of an or that is false is false
def Or.false_right(a: Bool, b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case False{}:
      x => x
    case True{}:
      x => Empty.absurd(
        {b == False{}: Bool},
        {(%x: {\{False: Empty; \{True: Unit; \{}}}: Bool -> Type}(_); Unit{}): Empty}
      )

# a path that is not among the paths of one path is not that path
def Near.one(
  +p: String,
  +r: String
) -> {
  List.contains(~String, ~String.eq, [p], r) == False{}: Bool
} -> {String.eq(p, r) == False{}: Bool}:
  x => Shared.List.any.if_false_hit(
    String.eq(p, r),
    u => List.contains(String, String.eq, [], r)
  )(x)

# files near files that are near a third are near the third at the paths
# of both, at each of the paths rs
def Near.trans.go(
  +x: Files.Files(),
  +y: Files.Files(),
  +z: Files.Files(),
  +ps: List<&2, String>,
  +qs: List<&2, String>,
  rs: List<&2, String>,
  +wx: {FileLaws.Files.wf(x) == True{}: Bool},
  +wy: {FileLaws.Files.wf(y) == True{}: Bool},
  +wz: {FileLaws.Files.wf(z) == True{}: Bool},
  +h1: {RContents.Near.files(x, y, ps) == True{}: Bool},
  +h2: {RContents.Near.files(y, z, qs) == True{}: Bool}
) -> {RContents.Near.files.go(x, z, List.append(&2, String, ps, qs), rs) == True{}: Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, List.append(&2, String, ps, qs), r),
          Formats.Content.same(Files.Files.get(x, r), Files.Files.get(z, r))
        ),
        RContents.Near.files.go(x, z, List.append(&2, String, ps, qs), rest)
      )(
        Near.at(
          x,
          z,
          List.append(&2, String, ps, qs),
          r,
          +hc => Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Files.Files.get(x, r),
            Files.Files.get(y, r),
            Files.Files.get(z, r),
            Near.out(
              x,
              y,
              ps,
              r
            )(
              wx
            )(
              wy
            )(
              h1
            )(
              Or.false_left(
                List.contains(~String, ~String.eq, ps, r),
                List.contains(~String, ~String.eq, qs, r)
              )(
                Equal.trans(
                  Bool,
                  Bool.or(
                    List.contains(~String, ~String.eq, ps, r),
                    List.contains(~String, ~String.eq, qs, r)
                  ),
                  List.contains(~String, ~String.eq, List.append(&2, String, ps, qs), r),
                  False{},
                  Equal.sym(
                    Bool,
                    List.contains(~String, ~String.eq, List.append(&2, String, ps, qs), r),
                    Bool.or(
                      List.contains(~String, ~String.eq, ps, r),
                      List.contains(~String, ~String.eq, qs, r)
                    ),
                    Shared.List.contains_append(~String, ~String.eq, ps, qs, r)
                  ),
                  hc
                )
              )
            ),
            Near.out(
              y,
              z,
              qs,
              r
            )(
              wy
            )(
              wz
            )(
              h2
            )(
              Or.false_right(
                List.contains(~String, ~String.eq, ps, r),
                List.contains(~String, ~String.eq, qs, r)
              )(
                Equal.trans(
                  Bool,
                  Bool.or(
                    List.contains(~String, ~String.eq, ps, r),
                    List.contains(~String, ~String.eq, qs, r)
                  ),
                  List.contains(~String, ~String.eq, List.append(&2, String, ps, qs), r),
                  False{},
                  Equal.sym(
                    Bool,
                    List.contains(~String, ~String.eq, List.append(&2, String, ps, qs), r),
                    Bool.or(
                      List.contains(~String, ~String.eq, ps, r),
                      List.contains(~String, ~String.eq, qs, r)
                    ),
                    Shared.List.contains_append(~String, ~String.eq, ps, qs, r)
                  ),
                  hc
                )
              )
            )
          )
        )
      )(Near.trans.go(x, y, z, ps, qs, rest, wx, wy, wz, h1, h2))

# files near files that are near a third are near the third at the paths
# of both
def Near.trans(
  +x: Files.Files(),
  +y: Files.Files(),
  +z: Files.Files(),
  +ps: List<&2, String>,
  +qs: List<&2, String>
) -> {
  FileLaws.Files.wf(x) == True{}: Bool
} -> {
  FileLaws.Files.wf(y) == True{}: Bool
} -> {
  FileLaws.Files.wf(z) == True{}: Bool
} -> {
  RContents.Near.files(x, y, ps) == True{}: Bool
} -> {
  RContents.Near.files(y, z, qs) == True{}: Bool
} -> {RContents.Near.files(x, z, List.append(&2, String, ps, qs)) == True{}: Bool}:
  wx => wy => wz => h1 => h2 => Near.trans.go(
    x,
    y,
    z,
    ps,
    qs,
    List.append(&2, String, Files.Files.paths(x), Files.Files.paths(z)),
    wx,
    wy,
    wz,
    h1,
    h2
  )

# a write at the path p holds what the files before it hold at each of the
# paths qs that is not p
def Near.set.go(
  +y: Files.Files(),
  +p: String,
  +w: Maybe<&2, List<&2, U32>>,
  qs: List<&2, String>,
  +wy: {FileLaws.Files.wf(y) == True{}: Bool}
) -> {RContents.Near.files.go(Files.Files.set(y, p, w), y, [p], qs) == True{}: Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, [p], r),
          Formats.Content.same(Files.Files.get(Files.Files.set(y, p, w), r), Files.Files.get(y, r))
        ),
        RContents.Near.files.go(Files.Files.set(y, p, w), y, [p], rest)
      )(
        Near.at(
          Files.Files.set(y, p, w),
          y,
          [p],
          r,
          hc => FileLaws.Files.get_set_other(y, p, w, r)(Near.one(p, r)(hc))(wy)
        )
      )(Near.set.go(y, p, w, rest, wy))

# a write at the path p is near the files before it at p
def Near.set(
  +y: Files.Files(),
  +p: String,
  +w: Maybe<&2, List<&2, U32>>
) -> {
  FileLaws.Files.wf(y) == True{}: Bool
} -> {RContents.Near.files(Files.Files.set(y, p, w), y, [p]) == True{}: Bool}:
  x => (%Equal.sym(
    Bool,
    RContents.Near.files.go(
      Files.Files.set(y, p, w),
      y,
      [p],
      List.append(&2, String, Files.Files.paths(Files.Files.set(y, p, w)), Files.Files.paths(y))
    ),
    True{},
    Near.set.go(
      y,
      p,
      w,
      List.append(&2, String, Files.Files.paths(Files.Files.set(y, p, w)), Files.Files.paths(y)),
      x
    )
  ): {_ == True{}: Bool}; {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the base holds no path that is none of the paths of a merge
def Paths.out_base(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String,
  wb: {FileLaws.Files.wf(b) == True{}: Bool}
) -> {
  List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p) == False{}: Bool
} -> {Files.Files.get(b, p) == None{}: Maybe<&2, List<&2, U32>>}:
  hc => Reads.Maybe.none_by(
    List<&2, U32>,
    Files.Files.get(b, p),
    ws => e => Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
        False{},
        Equal.sym(
          Bool,
          List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
          True{},
          Reads.Paths.base(b, o, t, p, ws, wb)(e)
        ),
        hc
      )
    )
  )

# ours holds no path that is none of the paths of a merge
def Paths.out_ours(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String,
  wo: {FileLaws.Files.wf(o) == True{}: Bool}
) -> {
  List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p) == False{}: Bool
} -> {Files.Files.get(o, p) == None{}: Maybe<&2, List<&2, U32>>}:
  hc => Reads.Maybe.none_by(
    List<&2, U32>,
    Files.Files.get(o, p),
    ws => e => Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
        False{},
        Equal.sym(
          Bool,
          List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
          True{},
          Reads.Paths.ours(b, o, t, p, ws, wo)(e)
        ),
        hc
      )
    )
  )

# theirs holds no path that is none of the paths of a merge
def Paths.out_theirs(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String,
  wt: {FileLaws.Files.wf(t) == True{}: Bool}
) -> {
  List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p) == False{}: Bool
} -> {Files.Files.get(t, p) == None{}: Maybe<&2, List<&2, U32>>}:
  hc => Reads.Maybe.none_by(
    List<&2, U32>,
    Files.Files.get(t, p),
    ws => e => Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
        False{},
        Equal.sym(
          Bool,
          List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), p),
          True{},
          Reads.Paths.theirs(b, o, t, p, ws, wt)(e)
        ),
        hc
      )
    )
  )

# a merge put at q leaves p as it was, when the merge of p clashes
def Merge.put_clash(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +acc: Files.Files(),
  +q: String,
  +p: String
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Files.Files.get(
    RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q)),
    p
  )
    == Files.Files.get(acc, p): Maybe<&2, List<&2, U32>>
}:
  wa => hm => Lists.Bool.by(
    d => {
      Files.Files.get(
        RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q)),
        p
      )
        == Files.Files.get(acc, p): Maybe<&2, List<&2, U32>>
    },
    String.eq(q, p),
    et => Reads.Eq.back(
      String,
      y => {
        Files.Files.get(
          RContents.Merge.put(acc, y, RContents.Merge.at(b, o, t, y)),
          p
        )
          == Files.Files.get(acc, p): Maybe<&2, List<&2, U32>>
      },
      q,
      p,
      Texts.String.eq_sound(q, p)(et),
      Reads.Eq.back(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        m => {
          Files.Files.get(
            RContents.Merge.put(acc, p, m),
            p
          )
            == Files.Files.get(acc, p): Maybe<&2, List<&2, U32>>
        },
        RContents.Merge.at(b, o, t, p),
        None{},
        hm,
        {==}
      )
    ),
    ef => Reads.Merge.put_other(acc, q, RContents.Merge.at(b, o, t, q), p)(wa)(ef)
  )

# the merges of the paths ps leave p as it was, when the merge of p clashes
def Merge.fold_clash(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>,
  +acc: Files.Files(),
  +p: String
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Files.Files.get(
    RContents.Merge.fold(b, o, t, ps, acc),
    p
  )
    == Files.Files.get(acc, p): Maybe<&2, List<&2, U32>>
}:
  match ps:
    case Nil{}:
      wa => hm => {==}
    case Con{+q, rest}:
      +wa => +hm => Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(
          RContents.Merge.fold(
            b,
            o,
            t,
            rest,
            RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q))
          ),
          p
        ),
        Files.Files.get(RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q)), p),
        Files.Files.get(acc, p),
        Merge.fold_clash(
          b,
          o,
          t,
          rest,
          RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q)),
          p
        )(Contents.Merge.put_wf(acc, q, RContents.Merge.at(b, o, t, q))(wa))(hm),
        Merge.put_clash(b, o, t, acc, q, p)(wa)(hm)
      )

# the merges of the paths ps read at p the merge x of p, when theirs holds
# at p what the base holds if p is none of ps
def Few.hit(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +p: String,
  +x: Maybe<&2, List<&2, U32>>,
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +hm: {RContents.Merge.at(b, o, t, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  out: {
    List.contains(~String, ~String.eq, ps, p) == False{}: Bool
  } -> {Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}
) -> {Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p) == x: Maybe<&2, List<&2, U32>>}:
  Lists.Bool.by(
    d => {Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p) == x: Maybe<&2, List<&2, U32>>},
    List.contains(~String, ~String.eq, ps, p),
    et => Reads.Merge.fold_in(b, o, t, ps, o, p, x)(wo)(hm)(et),
    ef => Reads.Merge.fold_keep(
      b,
      o,
      t,
      ps,
      o,
      p,
      x
    )(
      wo
    )(
      hm
    )(
      Shared.Maybe.some_inj(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(o, p),
        x,
        Equal.trans(
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Some{Files.Files.get(o, p)},
          RContents.Merge.at(b, o, t, p),
          Some{x},
          Equal.sym(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            RContents.Merge.at(b, o, t, p),
            Some{Files.Files.get(o, p)},
            Equal.trans(
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              RContents.Merge.at(b, o, t, p),
              Formats.Format.merge(
                p,
                Files.Files.get(b, p),
                Files.Files.get(o, p),
                Files.Files.get(b, p)
              ),
              Some{Files.Files.get(o, p)},
              Reads.Merge.at_as(
                b,
                o,
                t,
                p,
                Files.Files.get(b, p),
                Files.Files.get(o, p),
                Files.Files.get(b, p)
              )({==})({==})(out(ef)),
              Formats.Format.merge_ours(p, Files.Files.get(b, p), Files.Files.get(o, p))
            )
          ),
          hm
        )
      )
    )
  )

# the merge of the paths ps reads at p what the merge of every path reads,
# when theirs holds at p what the base holds if p is none of ps
def Few.get(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +p: String,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  out: {
    List.contains(~String, ~String.eq, ps, p) == False{}: Bool
  } -> {Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}
) -> {
  Files.Files.get(
    RContents.Merge.fold(b, o, t, ps, o),
    p
  )
    == Files.Files.get(RContents.Merge.files(b, o, t), p): Maybe<&2, List<&2, U32>>
}:
  Lists.Maybe.by(
    Maybe<&2, List<&2, U32>>,
    m => {
      Files.Files.get(
        RContents.Merge.fold(b, o, t, ps, o),
        p
      )
        == Files.Files.get(RContents.Merge.files(b, o, t), p): Maybe<&2, List<&2, U32>>
    },
    RContents.Merge.at(b, o, t, p),
    +en => Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p),
      Files.Files.get(o, p),
      Files.Files.get(RContents.Merge.files(b, o, t), p),
      Merge.fold_clash(b, o, t, ps, o, p)(wo)(en),
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(RContents.Merge.files(b, o, t), p),
        Files.Files.get(o, p),
        Merge.fold_clash(b, o, t, RContents.Merge.paths(b, o, t), o, p)(wo)(en)
      )
    ),
    +x => +es => Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p),
      x,
      Files.Files.get(RContents.Merge.files(b, o, t), p),
      Few.hit(b, o, t, ps, p, x, wo, es, out),
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(RContents.Merge.files(b, o, t), p),
        x,
        Reads.Merge.files_get(b, o, t, p, x, wb, wo, wt, es)
      )
    )
  )

# Clean files
# -----------
# An entry of the files counts only under the key of its path. The files of a
# version hold no other entry: what they hold under the key of a path is of
# that path. So the files are what a read of each path gives.

# the map of the files t
def Clean.crit(t: Files.Files()) -> Crits.Crit<Files.Files.Item>:
  match t:
    case Files.Files{d}:
      d

# the map of well formed files is well formed
def Clean.wf_crit(
  t: Files.Files()
) -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {Crits.Crit.wf(~Files.Files.Item, Clean.crit(t), 0n) == True{}: Bool}:
  match t:
    case Files.Files{d}:
      h => h

# files of one map are the same
def Clean.eq_crit(
  x: Files.Files(),
  y: Files.Files()
) -> {Clean.crit(x) == Clean.crit(y): Crits.Crit<Files.Files.Item>} -> {x == y: Files.Files()}:
  match x y:
    case Files.Files{a} Files.Files{b}:
      e => Equal.cong(Crits.Crit<Files.Files.Item>, Files.Files(), d => Files.Files{d}, a, b, e)

# the entry of the path p with the words m, if any
def Item.of(p: String, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Files.Files.Item>:
  match m:
    case None{}:
      None{}
    case Some{ws}:
      Some{Files.Files.Item{p, ws}}

# the entry m, if any, is of the path p
def Item.clean(m: Maybe<&2, Files.Files.Item>, p: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Files.Files.Item{q, ws}}:
      String.eq(q, p)

# what the files t hold under the key of the path p is of the path p
def Clean.at(t: Files.Files(), +p: String) -> Bool:
  Item.clean(Crits.Crit.get(Files.Files.Item, Clean.crit(t), Files.Files.key(p)), p)

# an entry of the path p is the entry of p with the words that a read gives
def Item.get_of(
  m: Maybe<&2, Files.Files.Item>,
  +p: String
) -> {
  Item.clean(m, p) == True{}: Bool
} -> {m == Item.of(p, Files.Files.get.of(m, p)): Maybe<&2, Files.Files.Item>}:
  match m:
    case None{}:
      h => {==}
    case Some{Files.Files.Item{+q, +ws}}:
      +h => Reads.Eq.back(
        Bool,
        d => {
          Some{
            Files.Files.Item{q, ws}
          }
            == Item.of(
              p,
              Bool.pick(Maybe<&2, List<&2, U32>>, d, Some{ws}, None{})
            ): Maybe<&2, Files.Files.Item>
        },
        String.eq(q, p),
        True{},
        h,
        Equal.cong(
          String,
          Maybe<&2, Files.Files.Item>,
          y => Some{Files.Files.Item{y, ws}},
          q,
          p,
          Texts.String.eq_sound(q, p)(h)
        )
      )

# clean files hold under the key of a path the entry of the words that a
# read of the path gives
def Clean.get_crit(
  t: Files.Files(),
  +p: String
) -> {
  Clean.at(t, p) == True{}: Bool
} -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(t),
    Files.Files.key(p)
  )
    == Item.of(p, Files.Files.get(t, p)): Maybe<&2, Files.Files.Item>
}:
  match t:
    case Files.Files{+d}:
      h => Item.get_of(Crits.Crit.get(Files.Files.Item, d, Files.Files.key(p)), p)(h)

# one of two entries, each of the path p when it is the one, is of the path p
def Pick.clean(
  c: Bool,
  -a: Maybe<&2, Files.Files.Item>,
  -b: Maybe<&2, Files.Files.Item>,
  -p: String
) -> (
  {c == True{}: Bool} -> {Item.clean(a, p) == True{}: Bool}
) -> (
  {c == False{}: Bool} -> {Item.clean(b, p) == True{}: Bool}
) -> {Item.clean(Bool.pick(Maybe<&2, Files.Files.Item>, c, a, b), p) == True{}: Bool}:
  match c:
    case True{}:
      f => g => f({==})
    case False{}:
      f => g => g({==})

# two paths of one key are the same
def Key.same_path(
  +q: String,
  +p: String
) -> {
  Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)) == True{}: Bool
} -> {String.eq(q, p) == True{}: Bool}:
  hk => Lists.Bool.by(
    d => {d == True{}: Bool},
    String.eq(q, p),
    et => {==},
    ef => Empty.absurd(
      {False{} == True{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)),
          False{},
          Equal.sym(Bool, Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)), True{}, hk),
          FileLaws.Files.key_ne(q, p)(ef)
        )
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a write keeps what the files hold under the key of the path p of the path p
def Clean.set(
  t: Files.Files(),
  +q: String,
  w: Maybe<&2, List<&2, U32>>,
  +p: String
) -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {Clean.at(t, p) == True{}: Bool} -> {Clean.at(Files.Files.set(t, q, w), p) == True{}: Bool}:
  match t w:
    case Files.Files{+d} None{}:
      wf => h => Reads.Eq.back(
        Maybe<&2, Files.Files.Item>,
        m => {Item.clean(m, p) == True{}: Bool},
        Crits.Crit.get(
          Files.Files.Item,
          Crits.Crit.drop(Files.Files.Item, d, Files.Files.key(q)),
          Files.Files.key(p)
        ),
        Bool.pick(
          Maybe<&2, Files.Files.Item>,
          Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)),
          None{},
          Crits.Crit.get(Files.Files.Item, d, Files.Files.key(p))
        ),
        Crits.Dict.get_drop.at(~Files.Files.Item, d, Files.Files.key(q), Files.Files.key(p))(wf),
        Pick.clean(
          Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)),
          None{},
          Crits.Crit.get(Files.Files.Item, d, Files.Files.key(p)),
          p
        )(hk => {==})(hf => h)
      )
    case Files.Files{+d} Some{+ws}:
      wf => h => Reads.Eq.back(
        Maybe<&2, Files.Files.Item>,
        m => {Item.clean(m, p) == True{}: Bool},
        Crits.Crit.get(
          Files.Files.Item,
          Crits.Crit.set(~Files.Files.Item, d, Files.Files.key(q), Files.Files.Item{q, ws}),
          Files.Files.key(p)
        ),
        Bool.pick(
          Maybe<&2, Files.Files.Item>,
          Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)),
          Some{Files.Files.Item{q, ws}},
          Crits.Crit.get(Files.Files.Item, d, Files.Files.key(p))
        ),
        Crits.Dict.get_set.at(
          ~Files.Files.Item,
          d,
          Files.Files.key(q),
          Files.Files.Item{q, ws},
          Files.Files.key(p)
        )(wf),
        Pick.clean(
          Crits.Key.is_eq(Files.Files.key(p), Files.Files.key(q)),
          Some{Files.Files.Item{q, ws}},
          Crits.Crit.get(Files.Files.Item, d, Files.Files.key(p)),
          p
        )(hk => Key.same_path(q, p)(hk))(hf => h)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a merge put keeps the files clean at the path p
def Merge.put_clean(
  acc: Files.Files(),
  +q: String,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  +p: String
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  Clean.at(acc, p) == True{}: Bool
} -> {Clean.at(RContents.Merge.put(acc, q, m), p) == True{}: Bool}:
  match m:
    case None{}:
      wa => h => h
    case Some{x}:
      wa => h => Clean.set(acc, q, x, p)(wa)(h)

# the merges of the paths ps keep the files clean at the path p
def Merge.fold_clean(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>,
  +acc: Files.Files(),
  +p: String
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  Clean.at(acc, p) == True{}: Bool
} -> {Clean.at(RContents.Merge.fold(b, o, t, ps, acc), p) == True{}: Bool}:
  match ps:
    case Nil{}:
      wa => h => h
    case Con{+q, rest}:
      +wa => h => Merge.fold_clean(
        b,
        o,
        t,
        rest,
        RContents.Merge.put(acc, q, RContents.Merge.at(b, o, t, q)),
        p
      )(
        Contents.Merge.put_wf(acc, q, RContents.Merge.at(b, o, t, q))(wa)
      )(Merge.put_clean(acc, q, RContents.Merge.at(b, o, t, q), p)(wa)(h))

# Paths by key
# ------------

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- this is said only in laws, and never runs
# the first of the paths ps whose key is q
def Keys.find(ps: List<&2, String>, +q: List<&2, U32>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      Bool.pick(
        Maybe<&2, String>,
        Crits.Key.is_eq(Files.Files.key(p), q),
        Some{p},
        Keys.find(rest, q)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the path that Keys.find gives has the key
def Keys.find_some(
  ps: List<&2, String>,
  +q: List<&2, U32>,
  +p: String
) -> {
  Keys.find(ps, q) == Some{p}: Maybe<&2, String>
} -> {Crits.Key.is_eq(Files.Files.key(p), q) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => Empty.absurd(
        {Crits.Key.is_eq(Files.Files.key(p), q) == True{}: Bool},
        Shared.Maybe.none_ne_some(String, p, h)
      )
    case Con{+p2, +rest}:
      h => Lists.Bool.by(
        d => {
          Bool.pick(
            Maybe<&2, String>,
            d,
            Some{p2},
            Keys.find(rest, q)
          )
            == Some{p}: Maybe<&2, String>
        } -> {Crits.Key.is_eq(Files.Files.key(p), q) == True{}: Bool},
        Crits.Key.is_eq(Files.Files.key(p2), q),
        et => h2 => Reads.Eq.to(
          String,
          y => {Crits.Key.is_eq(Files.Files.key(y), q) == True{}: Bool},
          p2,
          p,
          Shared.Maybe.some_inj(String, p2, p, h2),
          et
        ),
        ef => h2 => Keys.find_some(rest, q, p)(h2)
      )(h)

# no path of the first of two lists has a key that none of both has
def Keys.find_none_left(
  a: List<&2, String>,
  +b: List<&2, String>,
  +q: List<&2, U32>
) -> {
  Keys.find(List.append(&2, String, a, b), q) == None{}: Maybe<&2, String>
} -> {Keys.find(a, q) == None{}: Maybe<&2, String>}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+p, +rest}:
      h => Lists.Bool.by(
        d => {
          Bool.pick(
            Maybe<&2, String>,
            d,
            Some{p},
            Keys.find(List.append(&2, String, rest, b), q)
          )
            == None{}: Maybe<&2, String>
        } -> {
          Bool.pick(Maybe<&2, String>, d, Some{p}, Keys.find(rest, q)) == None{}: Maybe<&2, String>
        },
        Crits.Key.is_eq(Files.Files.key(p), q),
        et => h2 => h2,
        ef => h2 => Keys.find_none_left(rest, b, q)(h2)
      )(h)

# no path of the second of two lists has a key that none of both has
def Keys.find_none_right(
  a: List<&2, String>,
  +b: List<&2, String>,
  +q: List<&2, U32>
) -> {
  Keys.find(List.append(&2, String, a, b), q) == None{}: Maybe<&2, String>
} -> {Keys.find(b, q) == None{}: Maybe<&2, String>}:
  match a:
    case Nil{}:
      h => h
    case Con{+p, +rest}:
      h => Lists.Bool.by(
        d => {
          Bool.pick(
            Maybe<&2, String>,
            d,
            Some{p},
            Keys.find(List.append(&2, String, rest, b), q)
          )
            == None{}: Maybe<&2, String>
        } -> {Keys.find(b, q) == None{}: Maybe<&2, String>},
        Crits.Key.is_eq(Files.Files.key(p), q),
        et => h2 => Empty.absurd(
          {Keys.find(b, q) == None{}: Maybe<&2, String>},
          Crits.Crit.some_ne_none(String, p, h2)
        ),
        ef => h2 => Keys.find_none_right(rest, b, q)(h2)
      )(h)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- this is said only in laws, and never runs
# the files t are clean at each of the paths ps
def Clean.all(+t: Files.Files(), ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(Clean.at(t, p), Clean.all(t, rest))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# files that are clean at each of the paths ps are clean at the one that
# Keys.find gives
def Clean.all_find(
  +t: Files.Files(),
  ps: List<&2, String>,
  +q: List<&2, U32>,
  +p: String
) -> {
  Clean.all(t, ps) == True{}: Bool
} -> {Keys.find(ps, q) == Some{p}: Maybe<&2, String>} -> {Clean.at(t, p) == True{}: Bool}:
  match ps:
    case Nil{}:
      hc => h => Empty.absurd(
        {Clean.at(t, p) == True{}: Bool},
        Shared.Maybe.none_ne_some(String, p, h)
      )
    case Con{+p2, +rest}:
      +hc => h => Lists.Bool.by(
        d => {
          Bool.pick(
            Maybe<&2, String>,
            d,
            Some{p2},
            Keys.find(rest, q)
          )
            == Some{p}: Maybe<&2, String>
        } -> {Clean.at(t, p) == True{}: Bool},
        Crits.Key.is_eq(Files.Files.key(p2), q),
        et => h2 => Reads.Eq.to(
          String,
          y => {Clean.at(t, y) == True{}: Bool},
          p2,
          p,
          Shared.Maybe.some_inj(String, p2, p, h2),
          Shared.Bool.and_true_left(Clean.at(t, p2), Clean.all(t, rest))(hc)
        ),
        ef => h2 => Clean.all_find(
          t,
          rest,
          q,
          p
        )(Shared.Bool.and_true_right(Clean.at(t, p2), Clean.all(t, rest))(hc))(h2)
      )(h)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a write at the path p leaves what the files hold under another key
def Clean.set_miss(
  t: Files.Files(),
  +p: String,
  w: Maybe<&2, List<&2, U32>>,
  +q: List<&2, U32>
) -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {
  Crits.Key.is_eq(q, Files.Files.key(p)) == False{}: Bool
} -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(Files.Files.set(t, p, w)),
    q
  )
    == Crits.Crit.get(Files.Files.Item, Clean.crit(t), q): Maybe<&2, Files.Files.Item>
}:
  match t w:
    case Files.Files{+d} None{}:
      wf => hk => Equal.trans(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Crits.Crit.drop(Files.Files.Item, d, Files.Files.key(p)),
          q
        ),
        Bool.pick(
          Maybe<&2, Files.Files.Item>,
          Crits.Key.is_eq(q, Files.Files.key(p)),
          None{},
          Crits.Crit.get(Files.Files.Item, d, q)
        ),
        Crits.Crit.get(Files.Files.Item, d, q),
        Crits.Dict.get_drop.at(~Files.Files.Item, d, Files.Files.key(p), q)(wf),
        Reads.Eq.back(
          Bool,
          c => {
            Bool.pick(
              Maybe<&2, Files.Files.Item>,
              c,
              None{},
              Crits.Crit.get(Files.Files.Item, d, q)
            )
              == Crits.Crit.get(Files.Files.Item, d, q): Maybe<&2, Files.Files.Item>
          },
          Crits.Key.is_eq(q, Files.Files.key(p)),
          False{},
          hk,
          {==}
        )
      )
    case Files.Files{+d} Some{+ws}:
      wf => hk => Equal.trans(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Crits.Crit.set(~Files.Files.Item, d, Files.Files.key(p), Files.Files.Item{p, ws}),
          q
        ),
        Bool.pick(
          Maybe<&2, Files.Files.Item>,
          Crits.Key.is_eq(q, Files.Files.key(p)),
          Some{Files.Files.Item{p, ws}},
          Crits.Crit.get(Files.Files.Item, d, q)
        ),
        Crits.Crit.get(Files.Files.Item, d, q),
        Crits.Dict.get_set.at(
          ~Files.Files.Item,
          d,
          Files.Files.key(p),
          Files.Files.Item{p, ws},
          q
        )(wf),
        Reads.Eq.back(
          Bool,
          c => {
            Bool.pick(
              Maybe<&2, Files.Files.Item>,
              c,
              Some{Files.Files.Item{p, ws}},
              Crits.Crit.get(Files.Files.Item, d, q)
            )
              == Crits.Crit.get(Files.Files.Item, d, q): Maybe<&2, Files.Files.Item>
          },
          Crits.Key.is_eq(q, Files.Files.key(p)),
          False{},
          hk,
          {==}
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a merge put at the path p leaves what the files hold under another key
def Merge.put_miss(
  acc: Files.Files(),
  +p: String,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  +q: List<&2, U32>
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  Crits.Key.is_eq(q, Files.Files.key(p)) == False{}: Bool
} -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(RContents.Merge.put(acc, p, m)),
    q
  )
    == Crits.Crit.get(Files.Files.Item, Clean.crit(acc), q): Maybe<&2, Files.Files.Item>
}:
  match m:
    case None{}:
      wa => hk => {==}
    case Some{x}:
      wa => hk => Clean.set_miss(acc, p, x, q)(wa)(hk)

# one of Some and m is None only when it is m
def Pick.none_cond(
  c: Bool,
  -p: String,
  -m: Maybe<&2, String>
) -> {
  Bool.pick(Maybe<&2, String>, c, Some{p}, m) == None{}: Maybe<&2, String>
} -> {c == False{}: Bool}:
  match c:
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Crits.Crit.some_ne_none(String, p, h))
    case False{}:
      h => {==}

# one of Some and m that is None is m, which is None
def Pick.none_rest(
  c: Bool,
  -p: String,
  -m: Maybe<&2, String>
) -> {
  Bool.pick(Maybe<&2, String>, c, Some{p}, m) == None{}: Maybe<&2, String>
} -> {m == None{}: Maybe<&2, String>}:
  match c:
    case True{}:
      h => Empty.absurd({m == None{}: Maybe<&2, String>}, Crits.Crit.some_ne_none(String, p, h))
    case False{}:
      h => h

# the merges of the paths ps leave what the files hold under a key that is
# of none of ps
def Merge.fold_miss(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>,
  +acc: Files.Files(),
  +q: List<&2, U32>
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {
  Keys.find(ps, q) == None{}: Maybe<&2, String>
} -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(RContents.Merge.fold(b, o, t, ps, acc)),
    q
  )
    == Crits.Crit.get(Files.Files.Item, Clean.crit(acc), q): Maybe<&2, Files.Files.Item>
}:
  match ps:
    case Nil{}:
      wa => hn => {==}
    case Con{+p, +rest}:
      +wa => +hn => Equal.trans(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(
            RContents.Merge.fold(
              b,
              o,
              t,
              rest,
              RContents.Merge.put(acc, p, RContents.Merge.at(b, o, t, p))
            )
          ),
          q
        ),
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.put(acc, p, RContents.Merge.at(b, o, t, p))),
          q
        ),
        Crits.Crit.get(Files.Files.Item, Clean.crit(acc), q),
        Merge.fold_miss(
          b,
          o,
          t,
          rest,
          RContents.Merge.put(acc, p, RContents.Merge.at(b, o, t, p)),
          q
        )(
          Contents.Merge.put_wf(acc, p, RContents.Merge.at(b, o, t, p))(wa)
        )(Pick.none_rest(Crits.Key.is_eq(Files.Files.key(p), q), p, Keys.find(rest, q))(hn)),
        Merge.put_miss(
          acc,
          p,
          RContents.Merge.at(b, o, t, p),
          q
        )(
          wa
        )(
          Crits.Key.ne_sym(
            Files.Files.key(p),
            q
          )(Pick.none_cond(Crits.Key.is_eq(Files.Files.key(p), q), p, Keys.find(rest, q))(hn))
        )
      )

# The merge of a few paths is the merge of every path
# ---------------------------------------------------

# the merge of the paths ps holds under the key of p what the merge of every
# path holds, when ours is clean at p, and theirs holds at p what the base
# holds if p is none of ps
def Few.key(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +p: String,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hc: {Clean.at(o, p) == True{}: Bool},
  out: {
    List.contains(~String, ~String.eq, ps, p) == False{}: Bool
  } -> {Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}
) -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(RContents.Merge.fold(b, o, t, ps, o)),
    Files.Files.key(p)
  )
    == Crits.Crit.get(
      Files.Files.Item,
      Clean.crit(RContents.Merge.files(b, o, t)),
      Files.Files.key(p)
    ): Maybe<&2, Files.Files.Item>
}:
  Equal.trans(
    Maybe<&2, Files.Files.Item>,
    Crits.Crit.get(
      Files.Files.Item,
      Clean.crit(RContents.Merge.fold(b, o, t, ps, o)),
      Files.Files.key(p)
    ),
    Item.of(p, Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p)),
    Crits.Crit.get(
      Files.Files.Item,
      Clean.crit(RContents.Merge.files(b, o, t)),
      Files.Files.key(p)
    ),
    Clean.get_crit(
      RContents.Merge.fold(b, o, t, ps, o),
      p
    )(Merge.fold_clean(b, o, t, ps, o, p)(wo)(hc)),
    Equal.trans(
      Maybe<&2, Files.Files.Item>,
      Item.of(p, Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p)),
      Item.of(p, Files.Files.get(RContents.Merge.files(b, o, t), p)),
      Crits.Crit.get(
        Files.Files.Item,
        Clean.crit(RContents.Merge.files(b, o, t)),
        Files.Files.key(p)
      ),
      Equal.cong(
        Maybe<&2, List<&2, U32>>,
        Maybe<&2, Files.Files.Item>,
        m => Item.of(p, m),
        Files.Files.get(RContents.Merge.fold(b, o, t, ps, o), p),
        Files.Files.get(RContents.Merge.files(b, o, t), p),
        Few.get(b, o, t, ps, p, wb, wo, wt, out)
      ),
      Equal.sym(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, t)),
          Files.Files.key(p)
        ),
        Item.of(p, Files.Files.get(RContents.Merge.files(b, o, t), p)),
        Clean.get_crit(
          RContents.Merge.files(b, o, t),
          p
        )(Merge.fold_clean(b, o, t, RContents.Merge.paths(b, o, t), o, p)(wo)(hc))
      )
    )
  )

# the merge of the paths ps holds under each key what the merge of every
# path holds, when ours is clean at each path of both, and theirs holds what
# the base holds at each path that is none of ps
def Few.same_at(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +q: List<&2, U32>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hc: {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool},
  out: @p: String -> {
    List.contains(~String, ~String.eq, ps, p) == False{}: Bool
  } -> {Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}
) -> {
  Crits.Crit.get(
    Files.Files.Item,
    Clean.crit(RContents.Merge.fold(b, o, t, ps, o)),
    q
  )
    == Crits.Crit.get(
      Files.Files.Item,
      Clean.crit(RContents.Merge.files(b, o, t)),
      q
    ): Maybe<&2, Files.Files.Item>
}:
  Lists.Maybe.by(
    String,
    m => {
      Crits.Crit.get(
        Files.Files.Item,
        Clean.crit(RContents.Merge.fold(b, o, t, ps, o)),
        q
      )
        == Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, t)),
          q
        ): Maybe<&2, Files.Files.Item>
    },
    Keys.find(List.append(&2, String, ps, RContents.Merge.paths(b, o, t)), q),
    +en => Equal.trans(
      Maybe<&2, Files.Files.Item>,
      Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.fold(b, o, t, ps, o)), q),
      Crits.Crit.get(Files.Files.Item, Clean.crit(o), q),
      Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
      Merge.fold_miss(
        b,
        o,
        t,
        ps,
        o,
        q
      )(wo)(Keys.find_none_left(ps, RContents.Merge.paths(b, o, t), q)(en)),
      Equal.sym(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
        Crits.Crit.get(Files.Files.Item, Clean.crit(o), q),
        Merge.fold_miss(
          b,
          o,
          t,
          RContents.Merge.paths(b, o, t),
          o,
          q
        )(wo)(Keys.find_none_right(ps, RContents.Merge.paths(b, o, t), q)(en))
      )
    ),
    +p => +es => Reads.Eq.to(
      List<&2, U32>,
      k => {
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.fold(b, o, t, ps, o)),
          k
        )
          == Crits.Crit.get(
            Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, t)),
            k
          ): Maybe<&2, Files.Files.Item>
      },
      Files.Files.key(p),
      q,
      Crits.Key.is_eq_sound(
        Files.Files.key(p),
        q
      )(Keys.find_some(List.append(&2, String, ps, RContents.Merge.paths(b, o, t)), q, p)(es)),
      Few.key(
        b,
        o,
        t,
        ps,
        p,
        wb,
        wo,
        wt,
        Clean.all_find(
          o,
          List.append(&2, String, ps, RContents.Merge.paths(b, o, t)),
          q,
          p
        )(hc)(es),
        out(p)
      )
    )
  )

# the entries of the merge of the paths ps, and those of the merge of every
# path, hold the same under the key q, when theirs is near the base at ps
def Few.binds_at(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +q: List<&2, U32>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool},
  +hc: {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> {
  Orders.Binds.get(
    Files.Files.Item,
    Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps))),
    q
  )
    == Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
      q
    ): Maybe<&2, Files.Files.Item>
}:
  Equal.trans(
    Maybe<&2, Files.Files.Item>,
    Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps))),
      q
    ),
    Crits.Crit.lookup(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
    Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
      q
    ),
    Orders.Crit.get_entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
    Equal.trans(
      Maybe<&2, Files.Files.Item>,
      Crits.Crit.lookup(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
      Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
      Orders.Binds.get(
        Files.Files.Item,
        Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
        q
      ),
      Equal.sym(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
        Crits.Crit.lookup(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
        Crits.Crit.get_lookup(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, t, ps)),
          q
        )(
          Clean.wf_crit(
            RContents.Merge.few(b, o, t, ps)
          )(Contents.Merge.fold_wf(b, o, t, ps, o)(wo))
        )
      ),
      Equal.trans(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps)), q),
        Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
        Orders.Binds.get(
          Files.Files.Item,
          Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
          q
        ),
        Few.same_at(
          b,
          o,
          t,
          ps,
          q,
          wb,
          wo,
          wt,
          hc,
          p => ho => Near.out(t, b, ps, p)(wt)(wb)(hn)(ho)
        ),
        Equal.trans(
          Maybe<&2, Files.Files.Item>,
          Crits.Crit.get(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
          Crits.Crit.lookup(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
          Orders.Binds.get(
            Files.Files.Item,
            Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
            q
          ),
          Crits.Crit.get_lookup(
            ~Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, t)),
            q
          )(Clean.wf_crit(RContents.Merge.files(b, o, t))(Contents.Merge.files_wf(b, o, t)(wo))),
          Equal.sym(
            Maybe<&2, Files.Files.Item>,
            Orders.Binds.get(
              Files.Files.Item,
              Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
              q
            ),
            Crits.Crit.lookup(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q),
            Orders.Crit.get_entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)), q)
          )
        )
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the entries of the merge of the paths ps, and those of the merge of every
# path, hold the same under the key of each of the entries es, when theirs
# is near the base at ps
def Few.same(
  es: List<&2, Crits.Bind<Files.Files.Item>>,
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool},
  +hc: {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> Orders.Binds.Same(
  Files.Files.Item,
  es,
  Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps))),
  Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)))
):
  match es:
    case Nil{}:
      Unit{}
    case Con{Crits.Bind{+q, v}, rest}:
      (
        Few.binds_at(b, o, t, ps, q, wb, wo, wt, hn, hc),
        Few.same(rest, b, o, t, ps, wb, wo, wt, hn, hc)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the merge of the paths ps is the merge of every path, when theirs is near
# the base at ps, and ours is clean at each path of both
def Few.files(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool},
  +hc: {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> {RContents.Merge.few(b, o, t, ps) == RContents.Merge.files(b, o, t): Files.Files()}:
  Clean.eq_crit(
    RContents.Merge.few(b, o, t, ps),
    RContents.Merge.files(b, o, t)
  )(
    Crits.Crit.ext(
      ~Files.Files.Item,
      Clean.crit(RContents.Merge.few(b, o, t, ps)),
      Clean.crit(RContents.Merge.files(b, o, t))
    )(
      Clean.wf_crit(RContents.Merge.few(b, o, t, ps))(Contents.Merge.fold_wf(b, o, t, ps, o)(wo))
    )(
      Clean.wf_crit(RContents.Merge.files(b, o, t))(Contents.Merge.files_wf(b, o, t)(wo))
    )(
      Orders.Binds.ext(
        ~Files.Files.Item,
        Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps))),
        Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t)))
      )(
        Orders.Crit.entries_sorted(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, t, ps))
        )(
          Clean.wf_crit(
            RContents.Merge.few(b, o, t, ps)
          )(Contents.Merge.fold_wf(b, o, t, ps, o)(wo))
        )
      )(
        Orders.Crit.entries_sorted(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, t))
        )(Clean.wf_crit(RContents.Merge.files(b, o, t))(Contents.Merge.files_wf(b, o, t)(wo)))
      )(
        Few.same(
          Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.few(b, o, t, ps))),
          b,
          o,
          t,
          ps,
          wb,
          wo,
          wt,
          hn,
          hc
        )
      )(
        Few.same(
          Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, t))),
          b,
          o,
          t,
          ps,
          wb,
          wo,
          wt,
          hn,
          hc
        )
      )
    )
  )

# Clean contents
# --------------

# the content m, if the node holds it, is clean at the path p
def Content.clean(m: Maybe<&2, Files.Files()>, +p: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      Clean.at(t, p)

# a write keeps a content clean
def Content.write_clean(
  +q: String,
  w: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Files.Files()>,
  +p: String
) -> {
  Contents.Content.sound(m) == True{}: Bool
} -> {
  Content.clean(m, p) == True{}: Bool
} -> {Content.clean(RContents.Content.write(q, w, m), p) == True{}: Bool}:
  match m:
    case None{}:
      hs => h => {==}
    case Some{t}:
      hs => h => Clean.set(t, q, w, p)(hs)(h)

# the merge of a clean content is clean
def Merge.of_clean(
  fits: Bool,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>,
  +p: String
) -> {
  Contents.Content.sound(ours) == True{}: Bool
} -> {
  Content.clean(ours, p) == True{}: Bool
} -> {Content.clean(RContents.Merge.of(fits, ours, theirs, base), p) == True{}: Bool}:
  match fits ours theirs base:
    case True{} Some{+o} Some{+t} Some{+b}:
      hs => h => Merge.fold_clean(b, o, t, RContents.Merge.paths(b, o, t), o, p)(hs)(h)
    case True{} Some{o} Some{t} None{}:
      hs => h => {==}
    case True{} Some{o} None{} base:
      hs => h => {==}
    case True{} None{} theirs base:
      hs => h => {==}
    case False{} ours theirs base:
      hs => h => {==}

# a request keeps a content clean
def Content.apply_clean(
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>,
  +p: String
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Content.clean(prev, p) == True{}: Bool
} -> {
  Content.clean(other, p) == True{}: Bool
} -> {Content.clean(RContents.Content.apply(r, fits, prev, other, base), p) == True{}: Bool}:
  match r:
    case Spec.Request.Start{os}:
      hs => hp => ho => hp
    case Spec.Request.Write{b, q, w}:
      hs => hp => ho => Content.write_clean(q, w, prev, p)(hs)(hp)
    case Spec.Request.Merge{f, x}:
      hs => hp => ho => Merge.of_clean(fits, prev, other, base, p)(hs)(hp)
    case Spec.Request.Resolve{m, q, w}:
      hs => hp => ho => Content.write_clean(q, w, prev, p)(hs)(hp)
    case Spec.Request.Mark{b, m, v}:
      hs => hp => ho => hp
    case Spec.Request.Move{b, t, v}:
      hs => hp => ho => ho
    case Spec.Request.Group{h, g, ms}:
      hs => hp => ho => hp
    case Spec.Request.Own{c, g}:
      hs => hp => ho => hp

# a version keeps a content clean
def Content.next_clean(
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>,
  +p: String
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Content.clean(prev, p) == True{}: Bool
} -> {
  Content.clean(other, p) == True{}: Bool
} -> {Content.clean(RContents.Content.next(m, fits, prev, other, base), p) == True{}: Bool}:
  match m:
    case None{}:
      hs => hp => ho => {==}
    case Some{e}:
      hs => hp => ho => Content.apply_clean(
        RLines.Ask.request(RLines.Entry.ask(e)),
        fits,
        prev,
        other,
        base,
        p
      )(hs)(hp)(ho)

# the content of version 0 is clean
def Content.first_clean(
  m: Maybe<&2, Types.Entry>,
  +p: String
) -> {Content.clean(RContents.Content.first(m), p) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# the content of a version is clean
def Content.at_clean(
  +fuel: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> {Content.clean(RContents.Content.at(fuel, RKnown.Known.none(), s, c, k), p) == True{}: Bool}:
  match fuel k:
    case 0n k:
      {==}
    case 1n+f 0n:
      Content.first_clean(RLines.Line.at(s, c, 0n), p)
    case 1n+f 1n+j:
      Content.next_clean(
        RLines.Line.at(s, c, 1n+j),
        RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
        RContents.Content.at(f, RKnown.Known.none(), s, c, j),
        RContents.Content.at(
          f,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        ),
        RContents.Content.at(
          f,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
        ),
        p
      )(
        Contents.Content.at_sound(f, s, c, j)
      )(
        Content.at_clean(f, s, c, j, p)
      )(
        Content.at_clean(
          f,
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          p
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the files that are the content of a version are clean at each of the paths
# ps
def Content.at_clean_all(
  +fuel: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  ps: List<&2, String>,
  +o: Files.Files()
) -> {
  RContents.Content.at(fuel, RKnown.Known.none(), s, c, k) == Some{o}: Maybe<&2, Files.Files()>
} -> {Clean.all(o, ps) == True{}: Bool}:
  match ps:
    case Nil{}:
      e => {==}
    case Con{+p, +rest}:
      +e => Shared.Bool.and_both(
        Clean.at(o, p),
        Clean.all(o, rest)
      )(
        Reads.Eq.to(
          Maybe<&2, Files.Files()>,
          m => {Content.clean(m, p) == True{}: Bool},
          RContents.Content.at(fuel, RKnown.Known.none(), s, c, k),
          Some{o},
          e,
          Content.at_clean(fuel, s, c, k, p)
        )
      )(Content.at_clean_all(fuel, s, c, k, rest, o)(e))

# the merge of the paths ps is the merge of every path, when theirs is near
# the base at ps, and ours is clean
def Few.of(
  +ps: List<&2, String>,
  fits: Bool,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(ours) == True{}: Bool
} -> {
  Contents.Content.sound(theirs) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> (
  @o: Files.Files() -> @t: Files.Files() -> @b: Files.Files() -> {
    ours == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> {
  RContents.Merge.of.few(
    ps,
    fits,
    ours,
    theirs,
    base
  )
    == RContents.Merge.of(fits, ours, theirs, base): Maybe<&2, Files.Files()>
}:
  match fits ours theirs base:
    case True{} Some{+o} Some{+t} Some{+b}:
      wo => wt => wb => hn => hc => Equal.cong(
        Files.Files(),
        Maybe<&2, Files.Files()>,
        z => Some{z},
        RContents.Merge.few(b, o, t, ps),
        RContents.Merge.files(b, o, t),
        Few.files(b, o, t, ps, wb, wo, wt, hn(t)(b)({==})({==}), hc(o)(t)(b)({==})({==})({==}))
      )
    case True{} Some{o} Some{t} None{}:
      wo => wt => wb => hn => hc => {==}
    case True{} Some{o} None{} base:
      wo => wt => wb => hn => hc => {==}
    case True{} None{} theirs base:
      wo => wt => wb => hn => hc => {==}
    case False{} ours theirs base:
      wo => wt => wb => hn => hc => {==}

# a request that reads only the paths ps makes the content that it makes
# when it reads every path, when other is near base at ps
def Few.apply(
  +ps: List<&2, String>,
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Contents.Content.sound(other) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> (
  @o: Files.Files() -> @t: Files.Files() -> @b: Files.Files() -> {
    prev == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> {
  RContents.Content.apply.few(
    ps,
    r,
    fits,
    prev,
    other,
    base
  )
    == RContents.Content.apply(r, fits, prev, other, base): Maybe<&2, Files.Files()>
}:
  match r:
    case Spec.Request.Start{os}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Write{b, q, w}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Merge{f, x}:
      wo => wt => wb => hn => hc => Few.of(ps, fits, prev, other, base)(wo)(wt)(wb)(hn)(hc)
    case Spec.Request.Resolve{m, q, w}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Mark{b, m, v}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Move{b, t, v}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Group{h, g, ms}:
      wo => wt => wb => hn => hc => {==}
    case Spec.Request.Own{c, g}:
      wo => wt => wb => hn => hc => {==}

# a version that reads only the paths h, if known, has the content that it
# has when it reads every path: when other is near base at h, and prev is
# clean
def Few.next(
  h: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Contents.Content.sound(other) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @ps: List<
    &2,
    String> -> @t: Files.Files() -> @b: Files.Files() -> {
    h == Some{ps}: Maybe<&2, List<&2, String>>
  } -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> (
  @ps: List<
    &2,
    String> -> @o: Files.Files() -> @t: Files.Files() -> @b: Files.Files() -> {
    h == Some{ps}: Maybe<&2, List<&2, String>>
  } -> {
    prev == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {Clean.all(o, List.append(&2, String, ps, RContents.Merge.paths(b, o, t))) == True{}: Bool}
) -> {
  RContents.Content.quick(
    h,
    m,
    fits,
    prev,
    other,
    base
  )
    == RContents.Content.next(m, fits, prev, other, base): Maybe<&2, Files.Files()>
}:
  match h m:
    case None{} m:
      wo => wt => wb => hn => hc => {==}
    case Some{ps} None{}:
      wo => wt => wb => hn => hc => {==}
    case Some{+ps} Some{e}:
      wo => wt => wb => hn => hc => Few.apply(
        ps,
        RLines.Ask.request(RLines.Entry.ask(e)),
        fits,
        prev,
        other,
        base
      )(
        wo
      )(
        wt
      )(
        wb
      )(
        t => b => et => eb => hn(ps)(t)(b)({==})(et)(eb)
      )(o => t => b => ep => et => eb => hc(ps)(o)(t)(b)({==})(ep)(et)(eb))

# The clashes of a merge that reads a few paths
# ---------------------------------------------

# no path is among no paths
def Among.nil(ps: List<&2, String>) -> {RContents.Paths.among(ps, []) == []: List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, rest}:
      Among.nil(rest)

# the paths among ps that are among cs, read only when cs is not empty
def Among.few(
  cs: List<&2, String>,
  +ps: List<&2, String>
) -> {
  RContents.Merge.clashes.few.of(cs, u => ps) == RContents.Paths.among(ps, cs): List<&2, String>
}:
  match cs:
    case Nil{}:
      Equal.sym(List<&2, String>, RContents.Paths.among(ps, []), [], Among.nil(ps))
    case Con{p, rest}:
      {==}

# a Maybe that is none is None
def None.of(
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {
  Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, m) == True{}: Bool
} -> {m == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd(
        {Some{x} == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Bool.false_ne_true(h)
      )

# a path among the clashes of ps clashes
def Clash.sound(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>,
  +p: String
) -> {
  List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p) == True{}: Bool
} -> {RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match ps:
    case Nil{}:
      h => Empty.absurd(
        {RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+q, +rest}:
      h => Lists.Bool.by(
        d => {
          List.contains(
            ~String,
            ~String.eq,
            List.filter.put(String, q, RContents.Merge.clashes.go(b, o, t, rest), d),
            p
          )
            == True{}: Bool
        } -> {RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, RContents.Merge.at(b, o, t, q)),
        +et => h2 => Lists.Bool.by(
          e => {
            List.any.if(
              u => List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, rest), p),
              e
            )
              == True{}: Bool
          } -> {RContents.Merge.at(b, o, t, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
          String.eq(q, p),
          eq => h3 => Reads.Eq.to(
            String,
            y => {RContents.Merge.at(b, o, t, y) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
            q,
            p,
            Texts.String.eq_sound(q, p)(eq),
            None.of(RContents.Merge.at(b, o, t, q))(et)
          ),
          ne => h3 => Clash.sound(b, o, t, rest, p)(h3)
        )(h2),
        ef => h2 => Clash.sound(b, o, t, rest, p)(h2)
      )(h)

# the merge of a path that theirs left as the base is ours
def Merge.at_ours(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String
) -> {
  Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>
} -> {
  RContents.Merge.at(b, o, t, p) == Some{Files.Files.get(o, p)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  h => Equal.trans(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    RContents.Merge.at(b, o, t, p),
    Formats.Format.merge(p, Files.Files.get(b, p), Files.Files.get(o, p), Files.Files.get(b, p)),
    Some{Files.Files.get(o, p)},
    Reads.Merge.at_as(
      b,
      o,
      t,
      p,
      Files.Files.get(b, p),
      Files.Files.get(o, p),
      Files.Files.get(b, p)
    )({==})({==})(h),
    Formats.Format.merge_ours(p, Files.Files.get(b, p), Files.Files.get(o, p))
  )

# the merge of a path that ours left as the base is theirs
def Merge.at_theirs(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String
) -> {
  Files.Files.get(o, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>
} -> {
  RContents.Merge.at(b, o, t, p) == Some{Files.Files.get(t, p)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  x => (%Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Files.Files.get(o, p),
    Files.Files.get(b, p),
    x
  ): {
    Formats.Merge.pick(
      Shared.Maybe.is_eq(
        List<&2, U32>,
        Shared.List.is_eq(U32, U32.is_eq),
        _,
        Files.Files.get(b, p)
      ),
      Shared.Maybe.is_eq(
        List<&2, U32>,
        Shared.List.is_eq(U32, U32.is_eq),
        Files.Files.get(t, p),
        Files.Files.get(b, p)
      ),
      Shared.Maybe.is_eq(
        List<&2, U32>,
        Shared.List.is_eq(U32, U32.is_eq),
        _,
        Files.Files.get(t, p)
      ),
      p,
      Files.Files.get(b, p),
      _,
      Files.Files.get(t, p)
    )
      == Some{Files.Files.get(t, p)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }; Formats.Format.merge_theirs(p, Files.Files.get(b, p), Files.Files.get(t, p)))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the merge of every path holds what ours holds at each of the paths qs that
# is none of the paths ps, where theirs is near the base
def Near.ours.go(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  qs: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> {RContents.Near.files.go(RContents.Merge.files(b, o, t), o, ps, qs) == True{}: Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, ps, r),
          Formats.Content.same(
            Files.Files.get(RContents.Merge.files(b, o, t), r),
            Files.Files.get(o, r)
          )
        ),
        RContents.Near.files.go(RContents.Merge.files(b, o, t), o, ps, rest)
      )(
        Near.at(
          RContents.Merge.files(b, o, t),
          o,
          ps,
          r,
          hc => Reads.Merge.files_get(
            b,
            o,
            t,
            r,
            Files.Files.get(o, r),
            wb,
            wo,
            wt,
            Merge.at_ours(b, o, t, r)(Near.out(t, b, ps, r)(wt)(wb)(hn)(hc))
          )
        )
      )(Near.ours.go(b, o, t, ps, rest, wb, wo, wt, hn))

# the merge of every path is near ours at the paths ps, where theirs is near
# the base
def Near.ours(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {
  FileLaws.Files.wf(o) == True{}: Bool
} -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {
  RContents.Near.files(t, b, ps) == True{}: Bool
} -> {RContents.Near.files(RContents.Merge.files(b, o, t), o, ps) == True{}: Bool}:
  wb => wo => wt => hn => Near.ours.go(
    b,
    o,
    t,
    ps,
    List.append(
      &2,
      String,
      Files.Files.paths(RContents.Merge.files(b, o, t)),
      Files.Files.paths(o)
    ),
    wb,
    wo,
    wt,
    hn
  )

# the merge of every path holds what theirs holds at each of the paths qs
# that is none of the paths ps, where ours is near the base
def Near.theirs.go(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  qs: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(o, b, ps) == True{}: Bool}
) -> {RContents.Near.files.go(RContents.Merge.files(b, o, t), t, ps, qs) == True{}: Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, ps, r),
          Formats.Content.same(
            Files.Files.get(RContents.Merge.files(b, o, t), r),
            Files.Files.get(t, r)
          )
        ),
        RContents.Near.files.go(RContents.Merge.files(b, o, t), t, ps, rest)
      )(
        Near.at(
          RContents.Merge.files(b, o, t),
          t,
          ps,
          r,
          hc => Reads.Merge.files_get(
            b,
            o,
            t,
            r,
            Files.Files.get(t, r),
            wb,
            wo,
            wt,
            Merge.at_theirs(b, o, t, r)(Near.out(o, b, ps, r)(wo)(wb)(hn)(hc))
          )
        )
      )(Near.theirs.go(b, o, t, ps, rest, wb, wo, wt, hn))

# the merge of every path is near theirs at the paths ps, where ours is near
# the base
def Near.theirs(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {
  FileLaws.Files.wf(o) == True{}: Bool
} -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {
  RContents.Near.files(o, b, ps) == True{}: Bool
} -> {RContents.Near.files(RContents.Merge.files(b, o, t), t, ps) == True{}: Bool}:
  wb => wo => wt => hn => Near.theirs.go(
    b,
    o,
    t,
    ps,
    List.append(
      &2,
      String,
      Files.Files.paths(RContents.Merge.files(b, o, t)),
      Files.Files.paths(t)
    ),
    wb,
    wo,
    wt,
    hn
  )

# the merge of every path holds what ours holds at each of the paths qs that
# is none of the paths of the three merged
def Near.all_ours.go(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  qs: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool}
) -> {
  RContents.Near.files.go(
    RContents.Merge.files(b, o, t),
    o,
    RContents.Merge.paths(b, o, t),
    qs
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), r),
          Formats.Content.same(
            Files.Files.get(RContents.Merge.files(b, o, t), r),
            Files.Files.get(o, r)
          )
        ),
        RContents.Near.files.go(
          RContents.Merge.files(b, o, t),
          o,
          RContents.Merge.paths(b, o, t),
          rest
        )
      )(
        Near.at(
          RContents.Merge.files(b, o, t),
          o,
          RContents.Merge.paths(b, o, t),
          r,
          +hc => Reads.Merge.files_get(
            b,
            o,
            t,
            r,
            Files.Files.get(o, r),
            wb,
            wo,
            wt,
            Merge.at_ours(
              b,
              o,
              t,
              r
            )(
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                Files.Files.get(t, r),
                None{},
                Files.Files.get(b, r),
                Paths.out_theirs(b, o, t, r, wt)(hc),
                Equal.sym(
                  Maybe<&2, List<&2, U32>>,
                  Files.Files.get(b, r),
                  None{},
                  Paths.out_base(b, o, t, r, wb)(hc)
                )
              )
            )
          )
        )
      )(Near.all_ours.go(b, o, t, rest, wb, wo, wt))

# the merge of every path is near ours at the paths of the three merged
def Near.all_ours(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files()
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {
  FileLaws.Files.wf(o) == True{}: Bool
} -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {
  RContents.Near.files(
    RContents.Merge.files(b, o, t),
    o,
    RContents.Merge.paths(b, o, t)
  )
    == True{}: Bool
}:
  wb => wo => wt => Near.all_ours.go(
    b,
    o,
    t,
    List.append(
      &2,
      String,
      Files.Files.paths(RContents.Merge.files(b, o, t)),
      Files.Files.paths(o)
    ),
    wb,
    wo,
    wt
  )

# the merge of every path holds what theirs holds at each of the paths qs
# that is none of the paths of the three merged
def Near.all_theirs.go(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  qs: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool}
) -> {
  RContents.Near.files.go(
    RContents.Merge.files(b, o, t),
    t,
    RContents.Merge.paths(b, o, t),
    qs
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Shared.Bool.and_both(
        Bool.or(
          List.contains(~String, ~String.eq, RContents.Merge.paths(b, o, t), r),
          Formats.Content.same(
            Files.Files.get(RContents.Merge.files(b, o, t), r),
            Files.Files.get(t, r)
          )
        ),
        RContents.Near.files.go(
          RContents.Merge.files(b, o, t),
          t,
          RContents.Merge.paths(b, o, t),
          rest
        )
      )(
        Near.at(
          RContents.Merge.files(b, o, t),
          t,
          RContents.Merge.paths(b, o, t),
          r,
          +hc => Reads.Merge.files_get(
            b,
            o,
            t,
            r,
            Files.Files.get(t, r),
            wb,
            wo,
            wt,
            Merge.at_theirs(
              b,
              o,
              t,
              r
            )(
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                Files.Files.get(o, r),
                None{},
                Files.Files.get(b, r),
                Paths.out_ours(b, o, t, r, wo)(hc),
                Equal.sym(
                  Maybe<&2, List<&2, U32>>,
                  Files.Files.get(b, r),
                  None{},
                  Paths.out_base(b, o, t, r, wb)(hc)
                )
              )
            )
          )
        )
      )(Near.all_theirs.go(b, o, t, rest, wb, wo, wt))

# the merge of every path is near theirs at the paths of the three merged
def Near.all_theirs(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files()
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {
  FileLaws.Files.wf(o) == True{}: Bool
} -> {
  FileLaws.Files.wf(t) == True{}: Bool
} -> {
  RContents.Near.files(
    RContents.Merge.files(b, o, t),
    t,
    RContents.Merge.paths(b, o, t)
  )
    == True{}: Bool
}:
  wb => wo => wt => Near.all_theirs.go(
    b,
    o,
    t,
    List.append(
      &2,
      String,
      Files.Files.paths(RContents.Merge.files(b, o, t)),
      Files.Files.paths(t)
    ),
    wb,
    wo,
    wt
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a path clashes when it is among the clashes of the paths ps, and only
# then: when theirs holds what the base holds at each path that is none of ps
def Clash.same(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +p: String,
  out: {
    List.contains(~String, ~String.eq, ps, p) == False{}: Bool
  } -> {Files.Files.get(t, p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}
) -> {
  Maybe.is_none(
    &2,
    Maybe<&2, List<&2, U32>>,
    RContents.Merge.at(b, o, t, p)
  )
    == List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p): Bool
}:
  Lists.Bool.by(
    d => {
      d == List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p): Bool
    },
    Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, RContents.Merge.at(b, o, t, p)),
    +et => Equal.sym(
      Bool,
      List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p),
      True{},
      Reads.Merge.clashes_in(
        b,
        o,
        t,
        ps,
        p
      )(
        None.of(RContents.Merge.at(b, o, t, p))(et)
      )(
        Lists.Bool.by(
          d2 => {d2 == True{}: Bool},
          List.contains(~String, ~String.eq, ps, p),
          e2 => {==},
          e2 => Empty.absurd(
            {False{} == True{}: Bool},
            Shared.Bool.false_ne_true(
              Reads.Eq.to(
                Maybe<&2, Maybe<&2, List<&2, U32>>>,
                m => {Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, m) == True{}: Bool},
                RContents.Merge.at(b, o, t, p),
                Some{Files.Files.get(o, p)},
                Merge.at_ours(b, o, t, p)(out(e2)),
                et
              )
            )
          )
        )
      )
    ),
    +ef => Lists.Bool.by(
      d2 => {False{} == d2: Bool},
      List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p),
      e2 => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.true_ne_false(
          Reads.Eq.to(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            m => {Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, m) == False{}: Bool},
            RContents.Merge.at(b, o, t, p),
            None{},
            Clash.sound(b, o, t, ps, p)(e2),
            ef
          )
        )
      ),
      e2 => {==}
    )
  )

# the clashes among the paths rs are the paths of rs among the clashes of
# the paths ps, when theirs is near the base at ps
def Clash.among(
  rs: List<&2, String>,
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> {
  RContents.Merge.clashes.go(
    b,
    o,
    t,
    rs
  )
    == RContents.Paths.among(rs, RContents.Merge.clashes.go(b, o, t, ps)): List<&2, String>
}:
  match rs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      Reads.Eq.back(
        Bool,
        d => {
          List.filter.put(
            String,
            p,
            RContents.Merge.clashes.go(b, o, t, rest),
            d
          )
            == List.filter.put(
              String,
              p,
              RContents.Paths.among(rest, RContents.Merge.clashes.go(b, o, t, ps)),
              List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p)
            ): List<&2, String>
        },
        Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, RContents.Merge.at(b, o, t, p)),
        List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p),
        Clash.same(b, o, t, ps, p, ho => Near.out(t, b, ps, p)(wt)(wb)(hn)(ho)),
        Equal.cong(
          List<&2, String>,
          List<&2, String>,
          l => List.filter.put(
            String,
            p,
            l,
            List.contains(~String, ~String.eq, RContents.Merge.clashes.go(b, o, t, ps), p)
          ),
          RContents.Merge.clashes.go(b, o, t, rest),
          RContents.Paths.among(rest, RContents.Merge.clashes.go(b, o, t, ps)),
          Clash.among(rest, b, o, t, ps, wb, wt, hn)
        )
      )

# the clashes of a merge that reads the paths ps are the clashes of the
# merge of every path, when theirs is near the base at ps
def Few.clashes(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +ps: List<&2, String>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wt: {FileLaws.Files.wf(t) == True{}: Bool},
  +hn: {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> {
  RContents.Merge.clashes.few(b, o, t, ps) == RContents.Merge.clashes(b, o, t): List<&2, String>
}:
  Equal.trans(
    List<&2, String>,
    RContents.Merge.clashes.few(b, o, t, ps),
    RContents.Paths.among(RContents.Merge.paths(b, o, t), RContents.Merge.clashes.go(b, o, t, ps)),
    RContents.Merge.clashes(b, o, t),
    Among.few(RContents.Merge.clashes.go(b, o, t, ps), RContents.Merge.paths(b, o, t)),
    Equal.sym(
      List<&2, String>,
      RContents.Merge.clashes(b, o, t),
      RContents.Paths.among(
        RContents.Merge.paths(b, o, t),
        RContents.Merge.clashes.go(b, o, t, ps)
      ),
      Clash.among(RContents.Merge.paths(b, o, t), b, o, t, ps, wb, wt, hn)
    )
  )

# the clashes of a merge that fits, read from the paths ps, are those read
# from every path, when theirs is near base at ps
def Few.clashes_few(
  +ps: List<&2, String>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(base) == True{}: Bool
} -> {
  Contents.Content.sound(theirs) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> {
  RAnswers.Clashes.at.few(
    ps,
    fits,
    base,
    ours,
    theirs
  )
    == RAnswers.Clashes.at(fits, base, ours, theirs): Maybe<&2, List<&2, String>>
}:
  match fits base ours theirs:
    case True{} Some{+b} Some{+o} Some{+t}:
      wb => wt => hn => Equal.cong(
        List<&2, String>,
        Maybe<&2, List<&2, String>>,
        z => Some{z},
        RContents.Merge.clashes.few(b, o, t, ps),
        RContents.Merge.clashes(b, o, t),
        Few.clashes(b, o, t, ps, wb, wt, hn(t)(b)({==})({==}))
      )
    case True{} Some{b} Some{o} None{}:
      wb => wt => hn => {==}
    case True{} Some{b} None{} theirs:
      wb => wt => hn => {==}
    case True{} None{} ours theirs:
      wb => wt => hn => {==}
    case False{} base ours theirs:
      wb => wt => hn => {==}

# the clashes of a merge, read from the paths h, if known, are those read
# from every path, when theirs is near base at h
def Few.clashes_at(
  h: Maybe<&2, List<&2, String>>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(base) == True{}: Bool
} -> {
  Contents.Content.sound(theirs) == True{}: Bool
} -> (
  @ps: List<
    &2,
    String> -> @t: Files.Files() -> @b: Files.Files() -> {
    h == Some{ps}: Maybe<&2, List<&2, String>>
  } -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {RContents.Near.files(t, b, ps) == True{}: Bool}
) -> {
  RAnswers.Clashes.quick(
    h,
    fits,
    base,
    ours,
    theirs
  )
    == RAnswers.Clashes.at(fits, base, ours, theirs): Maybe<&2, List<&2, String>>
}:
  match h:
    case None{}:
      wb => wt => hn => {==}
    case Some{+ps}:
      wb => wt => hn => Few.clashes_few(
        ps,
        fits,
        base,
        ours,
        theirs
      )(wb)(wt)(t => b => et => eb => hn(ps)(t)(b)({==})(et)(eb))
