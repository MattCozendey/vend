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

# Merges of a few writes: laws
# ----------------------------
# A merge reads only the paths that what it takes changed from its base, when
# the node knows them (RContents.Merge.few). Here: when theirs is the base
# with some writes, the merge of the paths of those writes is the merge of
# every path (Few.files).

# the files b after the writes ws, the oldest first
def Writes.apply(ws: List<&2, RContents.Write>, b: Files.Files()) -> Files.Files():
  match ws:
    case Nil{}:
      b
    case Con{RContents.Write{p, w}, rest}:
      Writes.apply(rest, Files.Files.set(b, p, w))

# writes keep the files well formed
def Writes.apply_wf(
  ws: List<&2, RContents.Write>,
  +b: Files.Files()
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {FileLaws.Files.wf(Writes.apply(ws, b)) == True{}: Bool}:
  match ws:
    case Nil{}:
      h => h
    case Con{RContents.Write{+p, +w}, rest}:
      h => Writes.apply_wf(rest, Files.Files.set(b, p, w))(FileLaws.Files.set_wf(b, p, w)(h))

# writes leave a path that is none of theirs as it was
def Writes.apply_other(
  ws: List<&2, RContents.Write>,
  +b: Files.Files(),
  +p: String
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, RContents.Writes.paths(ws), p) == False{}: Bool
} -> {Files.Files.get(Writes.apply(ws, b), p) == Files.Files.get(b, p): Maybe<&2, List<&2, U32>>}:
  match ws:
    case Nil{}:
      h => hc => {==}
    case Con{RContents.Write{+q, +w}, +rest}:
      +h => +hc => Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Files.Files.get(Writes.apply(rest, Files.Files.set(b, q, w)), p),
        Files.Files.get(Files.Files.set(b, q, w), p),
        Files.Files.get(b, p),
        Writes.apply_other(
          rest,
          Files.Files.set(b, q, w),
          p
        )(
          FileLaws.Files.set_wf(b, q, w)(h)
        )(
          Shared.List.any.if_false_rest(
            String.eq(q, p),
            u => List.contains(~String, ~String.eq, RContents.Writes.paths(rest), p)
          )(hc)
        ),
        FileLaws.Files.get_set_other(
          b,
          q,
          w,
          p
        )(
          Shared.List.any.if_false_hit(
            String.eq(q, p),
            u => List.contains(~String, ~String.eq, RContents.Writes.paths(rest), p)
          )(hc)
        )(h)
      )

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

# the entries of the merge of the paths of the writes ws, and those of the
# merge of every path, hold the same under the key q, when theirs is the
# base with the writes
def Few.binds_at(
  +b: Files.Files(),
  +o: Files.Files(),
  +ws: List<&2, RContents.Write>,
  +q: List<&2, U32>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +hc: {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
) -> {
  Orders.Binds.get(
    Files.Files.Item,
    Crits.Crit.entries(
      Files.Files.Item,
      Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
    ),
    q
  )
    == Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(
        Files.Files.Item,
        Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
      ),
      q
    ): Maybe<&2, Files.Files.Item>
}:
  Equal.trans(
    Maybe<&2, Files.Files.Item>,
    Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(
        Files.Files.Item,
        Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
      ),
      q
    ),
    Crits.Crit.lookup(
      Files.Files.Item,
      Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
      q
    ),
    Orders.Binds.get(
      Files.Files.Item,
      Crits.Crit.entries(
        Files.Files.Item,
        Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
      ),
      q
    ),
    Orders.Crit.get_entries(
      Files.Files.Item,
      Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
      q
    ),
    Equal.trans(
      Maybe<&2, Files.Files.Item>,
      Crits.Crit.lookup(
        Files.Files.Item,
        Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
        q
      ),
      Crits.Crit.get(
        Files.Files.Item,
        Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
        q
      ),
      Orders.Binds.get(
        Files.Files.Item,
        Crits.Crit.entries(
          Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
        ),
        q
      ),
      Equal.sym(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
          q
        ),
        Crits.Crit.lookup(
          Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
          q
        ),
        Crits.Crit.get_lookup(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
          q
        )(
          Clean.wf_crit(
            RContents.Merge.few(b, o, Writes.apply(ws, b), ws)
          )(Contents.Merge.fold_wf(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws), o)(wo))
        )
      ),
      Equal.trans(
        Maybe<&2, Files.Files.Item>,
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
          q
        ),
        Crits.Crit.get(
          Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
          q
        ),
        Orders.Binds.get(
          Files.Files.Item,
          Crits.Crit.entries(
            Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
          ),
          q
        ),
        Few.same_at(
          b,
          o,
          Writes.apply(ws, b),
          RContents.Writes.paths(ws),
          q,
          wb,
          wo,
          Writes.apply_wf(ws, b)(wb),
          hc,
          p => ho => Writes.apply_other(ws, b, p)(wb)(ho)
        ),
        Equal.trans(
          Maybe<&2, Files.Files.Item>,
          Crits.Crit.get(
            Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
            q
          ),
          Crits.Crit.lookup(
            Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
            q
          ),
          Orders.Binds.get(
            Files.Files.Item,
            Crits.Crit.entries(
              Files.Files.Item,
              Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
            ),
            q
          ),
          Crits.Crit.get_lookup(
            ~Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
            q
          )(
            Clean.wf_crit(
              RContents.Merge.files(b, o, Writes.apply(ws, b))
            )(Contents.Merge.files_wf(b, o, Writes.apply(ws, b))(wo))
          ),
          Equal.sym(
            Maybe<&2, Files.Files.Item>,
            Orders.Binds.get(
              Files.Files.Item,
              Crits.Crit.entries(
                Files.Files.Item,
                Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
              ),
              q
            ),
            Crits.Crit.lookup(
              Files.Files.Item,
              Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
              q
            ),
            Orders.Crit.get_entries(
              Files.Files.Item,
              Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))),
              q
            )
          )
        )
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the entries of the merge of the paths of the writes ws, and those of the
# merge of every path, hold the same under the key of each of the entries es
def Few.same(
  es: List<&2, Crits.Bind<Files.Files.Item>>,
  +b: Files.Files(),
  +o: Files.Files(),
  +ws: List<&2, RContents.Write>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +hc: {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
) -> Orders.Binds.Same(
  Files.Files.Item,
  es,
  Crits.Crit.entries(
    Files.Files.Item,
    Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
  ),
  Crits.Crit.entries(Files.Files.Item, Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b))))
):
  match es:
    case Nil{}:
      Unit{}
    case Con{Crits.Bind{+q, v}, rest}:
      (Few.binds_at(b, o, ws, q, wb, wo, hc), Few.same(rest, b, o, ws, wb, wo, hc))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the merge of the paths of the writes ws is the merge of every path, when
# theirs is the base with the writes, and ours is clean at each path of both
def Few.files(
  +b: Files.Files(),
  +o: Files.Files(),
  +ws: List<&2, RContents.Write>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool},
  +wo: {FileLaws.Files.wf(o) == True{}: Bool},
  +hc: {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
) -> {
  RContents.Merge.few(
    b,
    o,
    Writes.apply(ws, b),
    ws
  )
    == RContents.Merge.files(b, o, Writes.apply(ws, b)): Files.Files()
}:
  Clean.eq_crit(
    RContents.Merge.few(b, o, Writes.apply(ws, b), ws),
    RContents.Merge.files(b, o, Writes.apply(ws, b))
  )(
    Crits.Crit.ext(
      ~Files.Files.Item,
      Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws)),
      Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
    )(
      Clean.wf_crit(
        RContents.Merge.few(b, o, Writes.apply(ws, b), ws)
      )(Contents.Merge.fold_wf(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws), o)(wo))
    )(
      Clean.wf_crit(
        RContents.Merge.files(b, o, Writes.apply(ws, b))
      )(Contents.Merge.files_wf(b, o, Writes.apply(ws, b))(wo))
    )(
      Orders.Binds.ext(
        ~Files.Files.Item,
        Crits.Crit.entries(
          Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
        ),
        Crits.Crit.entries(
          Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
        )
      )(
        Orders.Crit.entries_sorted(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
        )(
          Clean.wf_crit(
            RContents.Merge.few(b, o, Writes.apply(ws, b), ws)
          )(Contents.Merge.fold_wf(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws), o)(wo))
        )
      )(
        Orders.Crit.entries_sorted(
          ~Files.Files.Item,
          Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
        )(
          Clean.wf_crit(
            RContents.Merge.files(b, o, Writes.apply(ws, b))
          )(Contents.Merge.files_wf(b, o, Writes.apply(ws, b))(wo))
        )
      )(
        Few.same(
          Crits.Crit.entries(
            Files.Files.Item,
            Clean.crit(RContents.Merge.few(b, o, Writes.apply(ws, b), ws))
          ),
          b,
          o,
          ws,
          wb,
          wo,
          hc
        )
      )(
        Few.same(
          Crits.Crit.entries(
            Files.Files.Item,
            Clean.crit(RContents.Merge.files(b, o, Writes.apply(ws, b)))
          ),
          b,
          o,
          ws,
          wb,
          wo,
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

# A version after a few writes
# ----------------------------

# the content m, if the node holds it, after the writes ws
def Writes.over(
  ws: List<&2, RContents.Write>,
  m: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{Writes.apply(ws, b)}

# a content after no write is the content
def Writes.over_nil(
  m: Maybe<&2, Files.Files()>
) -> {m == Writes.over([], m): Maybe<&2, Files.Files()>}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

# a content after a write and then the writes ws is the content after the
# write, after ws
def Writes.over_step(
  ws: List<&2, RContents.Write>,
  q: String,
  w: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Files.Files()>
) -> {
  Writes.over(
    RContents.Write{q, w} <> ws,
    m
  )
    == Writes.over(ws, RContents.Content.write(q, w, m)): Maybe<&2, Files.Files()>
}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

# after the first n of xs come x and then r: x is at n
def Drop.head(
  xs: List<&2, Types.Entry>,
  n: Nat,
  -x: Types.Entry,
  -r: List<&2, Types.Entry>
) -> {
  List.drop(&2, Types.Entry, xs, n) == x <> r: List<&2, Types.Entry>
} -> {List.get(&2, Types.Entry, xs, n) == Some{x}: Maybe<&2, Types.Entry>}:
  match xs n:
    case Nil{} m:
      e => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, Types.Entry>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            List<&2, Types.Entry>,
            Bool,
            l => List.is_empty(&2, Types.Entry, l),
            x <> r,
            [],
            Equal.sym(List<&2, Types.Entry>, [], x <> r, e)
          )
        )
      )
    case Con{h, t} 0n:
      e => Equal.cong(
        List<&2, Types.Entry>,
        Maybe<&2, Types.Entry>,
        l => List.get(&2, Types.Entry, l, 0n),
        h <> t,
        x <> r,
        e
      )
    case Con{h, t} 1n+m:
      e => Drop.head(t, m, x, r)(e)

# the content of the version after j of the line c, the entry m if the node
# holds it, read with the fuel 1+g
def Next.of(
  +g: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +m: Maybe<&2, Types.Entry>
) -> Maybe<&2, Files.Files()>:
  RContents.Content.next(
    m,
    RContents.Entry.fits(RKnown.Known.none(), s, c, j, m),
    RContents.Content.at(g, RKnown.Known.none(), s, c, j),
    RContents.Content.at(
      g,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.taken(c, m)),
      Spec.Point.n(RContents.Entry.taken(c, m))
    ),
    RContents.Content.at(
      g,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.based(c, m)),
      Spec.Point.n(RContents.Entry.based(c, m))
    )
  )

# a content top that is what the request r makes of the content prev, after
# the writes that follow it (m), is prev after the write of r and those
# writes
def Writes.put_at(
  r: Spec.Request,
  -fits: Bool,
  +prev: Maybe<&2, Files.Files()>,
  -other: Maybe<&2, Files.Files()>,
  -base: Maybe<&2, Files.Files()>,
  m: Maybe<&2, List<&2, RContents.Write>>,
  +ws: List<&2, RContents.Write>,
  -top: Maybe<&2, Files.Files()>
) -> {
  RContents.Request.wrote(r, u => m) == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
} -> (
  @ws2: List<
    &2,
    RContents.Write> -> {
    m == Some{ws2}: Maybe<&2, List<&2, RContents.Write>>
  } -> {
    top
      == Writes.over(
        ws2,
        RContents.Content.apply(r, fits, prev, other, base)
      ): Maybe<&2, Files.Files()>
  }
) -> {top == Writes.over(ws, prev): Maybe<&2, Files.Files()>}:
  match r m:
    case Spec.Request.Start{os} m:
      h => ih => ih(ws)(h)
    case Spec.Request.Write{b, q, w} None{}:
      h => ih => Empty.absurd(
        {top == Writes.over(ws, prev): Maybe<&2, Files.Files()>},
        Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h)
      )
    case Spec.Request.Write{b, +q, +w} Some{+ws2}:
      h => ih => Reads.Eq.to(
        List<&2, RContents.Write>,
        y => {top == Writes.over(y, prev): Maybe<&2, Files.Files()>},
        RContents.Write{q, w} <> ws2,
        ws,
        Shared.Maybe.some_inj(List<&2, RContents.Write>, RContents.Write{q, w} <> ws2, ws, h),
        Equal.trans(
          Maybe<&2, Files.Files()>,
          top,
          Writes.over(ws2, RContents.Content.write(q, w, prev)),
          Writes.over(RContents.Write{q, w} <> ws2, prev),
          ih(ws2)({==}),
          Equal.sym(
            Maybe<&2, Files.Files()>,
            Writes.over(RContents.Write{q, w} <> ws2, prev),
            Writes.over(ws2, RContents.Content.write(q, w, prev)),
            Writes.over_step(ws2, q, w, prev)
          )
        )
      )
    case Spec.Request.Merge{f, x} m:
      h => ih => Empty.absurd(
        {top == Writes.over(ws, prev): Maybe<&2, Files.Files()>},
        Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h)
      )
    case Spec.Request.Resolve{b, q, w} None{}:
      h => ih => Empty.absurd(
        {top == Writes.over(ws, prev): Maybe<&2, Files.Files()>},
        Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h)
      )
    case Spec.Request.Resolve{b, +q, +w} Some{+ws2}:
      h => ih => Reads.Eq.to(
        List<&2, RContents.Write>,
        y => {top == Writes.over(y, prev): Maybe<&2, Files.Files()>},
        RContents.Write{q, w} <> ws2,
        ws,
        Shared.Maybe.some_inj(List<&2, RContents.Write>, RContents.Write{q, w} <> ws2, ws, h),
        Equal.trans(
          Maybe<&2, Files.Files()>,
          top,
          Writes.over(ws2, RContents.Content.write(q, w, prev)),
          Writes.over(RContents.Write{q, w} <> ws2, prev),
          ih(ws2)({==}),
          Equal.sym(
            Maybe<&2, Files.Files()>,
            Writes.over(RContents.Write{q, w} <> ws2, prev),
            Writes.over(ws2, RContents.Content.write(q, w, prev)),
            Writes.over_step(ws2, q, w, prev)
          )
        )
      )
    case Spec.Request.Mark{b, k, v} m:
      h => ih => ih(ws)(h)
    case Spec.Request.Move{b, t, v} m:
      h => ih => Empty.absurd(
        {top == Writes.over(ws, prev): Maybe<&2, Files.Files()>},
        Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h)
      )
    case Spec.Request.Group{hh, gg, ms} m:
      h => ih => ih(ws)(h)
    case Spec.Request.Own{cc, gg} m:
      h => ih => ih(ws)(h)

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# the content of a version, n versions after version j of its line, is the
# content of version j after the writes of the n versions between them, when
# each changes at most one path: es is the versions after j, and vs all the
# versions of the line
def Writes.at(
  n: Nat,
  es: List<&2, Types.Entry>,
  +g: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +vs: List<&2, Types.Entry>,
  +ws: List<&2, RContents.Write>
) -> {
  RLines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.drop(&2, Types.Entry, vs, 1n+j) == es: List<&2, Types.Entry>
} -> {
  RContents.Writes.of(n, es) == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
} -> {
  RContents.Content.at(
    Nat.add(n, g),
    RKnown.Known.none(),
    s,
    c,
    Nat.add(n, j)
  )
    == Writes.over(
      ws,
      RContents.Content.at(g, RKnown.Known.none(), s, c, j)
    ): Maybe<&2, Files.Files()>
}:
  match n es:
    case 0n es:
      hv => he => h => Reads.Eq.to(
        List<&2, RContents.Write>,
        y => {
          RContents.Content.at(
            g,
            RKnown.Known.none(),
            s,
            c,
            j
          )
            == Writes.over(
              y,
              RContents.Content.at(g, RKnown.Known.none(), s, c, j)
            ): Maybe<&2, Files.Files()>
        },
        [],
        ws,
        Shared.Maybe.some_inj(List<&2, RContents.Write>, [], ws, h),
        Writes.over_nil(RContents.Content.at(g, RKnown.Known.none(), s, c, j))
      )
    case 1n+d Nil{}:
      hv => he => h => Empty.absurd(
        {
          RContents.Content.at(
            1n+Nat.add(d, g),
            RKnown.Known.none(),
            s,
            c,
            1n+Nat.add(d, j)
          )
            == Writes.over(
              ws,
              RContents.Content.at(g, RKnown.Known.none(), s, c, j)
            ): Maybe<&2, Files.Files()>
        },
        Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h)
      )
    case 1n+(+d) Con{Types.Entry{Types.Pick{Types.Ask{+i, +k0, +r}, +pins}, +slot}, +rest}:
      +hv => +he => h => Writes.put_at(
        r,
        RContents.Entry.fits(
          RKnown.Known.none(),
          s,
          c,
          j,
          Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}}
        ),
        RContents.Content.at(g, RKnown.Known.none(), s, c, j),
        RContents.Content.at(
          g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(
            RContents.Entry.taken(c, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}})
          ),
          Spec.Point.n(
            RContents.Entry.taken(c, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}})
          )
        ),
        RContents.Content.at(
          g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(
            RContents.Entry.based(c, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}})
          ),
          Spec.Point.n(
            RContents.Entry.based(c, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}})
          )
        ),
        RContents.Writes.of(d, rest),
        ws,
        RContents.Content.at(1n+Nat.add(d, g), RKnown.Known.none(), s, c, 1n+Nat.add(d, j))
      )(
        h
      )(
        ws2 => e2 => Equal.trans(
          Maybe<&2, Files.Files()>,
          RContents.Content.at(1n+Nat.add(d, g), RKnown.Known.none(), s, c, 1n+Nat.add(d, j)),
          Writes.over(ws2, RContents.Content.at(1n+g, RKnown.Known.none(), s, c, 1n+j)),
          Writes.over(
            ws2,
            Next.of(g, s, c, j, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}})
          ),
          Reads.Eq.to(
            Nat,
            x => {
              RContents.Content.at(
                x,
                RKnown.Known.none(),
                s,
                c,
                1n+Nat.add(d, j)
              )
                == Writes.over(
                  ws2,
                  RContents.Content.at(1n+g, RKnown.Known.none(), s, c, 1n+j)
                ): Maybe<&2, Files.Files()>
            },
            Nat.add(d, 1n+g),
            1n+Nat.add(d, g),
            Shared.Nat.add_succ(d, g),
            Reads.Eq.to(
              Nat,
              y => {
                RContents.Content.at(
                  Nat.add(d, 1n+g),
                  RKnown.Known.none(),
                  s,
                  c,
                  y
                )
                  == Writes.over(
                    ws2,
                    RContents.Content.at(1n+g, RKnown.Known.none(), s, c, 1n+j)
                  ): Maybe<&2, Files.Files()>
              },
              Nat.add(d, 1n+j),
              1n+Nat.add(d, j),
              Shared.Nat.add_succ(d, j),
              Writes.at(
                d,
                rest,
                1n+g,
                s,
                c,
                1n+j,
                vs,
                ws2
              )(
                hv
              )(
                Shared.List.drop_step(
                  &2,
                  Types.Entry,
                  vs,
                  1n+j,
                  Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot},
                  rest
                )(he)
              )(e2)
            )
          ),
          Equal.cong(
            Maybe<&2, Files.Files()>,
            Maybe<&2, Files.Files()>,
            y => Writes.over(ws2, y),
            RContents.Content.at(1n+g, RKnown.Known.none(), s, c, 1n+j),
            Next.of(g, s, c, j, Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}}),
            Reads.Eq.to(
              Maybe<&2, Types.Entry>,
              m => {
                RContents.Content.at(
                  1n+g,
                  RKnown.Known.none(),
                  s,
                  c,
                  1n+j
                )
                  == Next.of(g, s, c, j, m): Maybe<&2, Files.Files()>
              },
              RLines.Line.at(s, c, 1n+j),
              Some{Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}},
              Reads.Eq.back(
                Maybe<&2, List<&2, Types.Entry>>,
                m => {
                  RLines.Line.at.of(
                    m,
                    1n+j
                  )
                    == Some{
                      Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot}
                    }: Maybe<&2, Types.Entry>
                },
                RLines.Line.versions(s, c),
                Some{vs},
                hv,
                Drop.head(
                  vs,
                  1n+j,
                  Types.Entry{Types.Pick{Types.Ask{i, k0, r}, pins}, slot},
                  rest
                )(he)
              ),
              {==}
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# A merge that reads a few paths
# ------------------------------

# the merge of the paths of the writes ws is the merge of every path, when
# theirs is the base with the writes, and ours is clean
def Few.of(
  +ws: List<&2, RContents.Write>,
  fits: Bool,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(ours) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {base == Some{b}: Maybe<&2, Files.Files()>} -> {t == Writes.apply(ws, b): Files.Files()}
) -> (
  @o: Files.Files() -> @b: Files.Files() -> {
    ours == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
) -> {
  RContents.Merge.of.few(
    ws,
    fits,
    ours,
    theirs,
    base
  )
    == RContents.Merge.of(fits, ours, theirs, base): Maybe<&2, Files.Files()>
}:
  match fits ours theirs base:
    case True{} Some{+o} Some{+t} Some{+b}:
      wo => wb => hr => hc => Reads.Eq.back(
        Files.Files(),
        y => {
          Some{
            RContents.Merge.few(b, o, y, ws)
          }
            == Some{RContents.Merge.files(b, o, y)}: Maybe<&2, Files.Files()>
        },
        t,
        Writes.apply(ws, b),
        hr(t)(b)({==})({==}),
        Equal.cong(
          Files.Files(),
          Maybe<&2, Files.Files()>,
          z => Some{z},
          RContents.Merge.few(b, o, Writes.apply(ws, b), ws),
          RContents.Merge.files(b, o, Writes.apply(ws, b)),
          Few.files(b, o, ws, wb, wo, hc(o)(b)({==})({==}))
        )
      )
    case True{} Some{o} Some{t} None{}:
      wo => wb => hr => hc => {==}
    case True{} Some{o} None{} base:
      wo => wb => hr => hc => {==}
    case True{} None{} theirs base:
      wo => wb => hr => hc => {==}
    case False{} ours theirs base:
      wo => wb => hr => hc => {==}

# a request that reads only the paths of the writes ws makes the content
# that it makes when it reads every path
def Few.apply(
  +ws: List<&2, RContents.Write>,
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {base == Some{b}: Maybe<&2, Files.Files()>} -> {t == Writes.apply(ws, b): Files.Files()}
) -> (
  @o: Files.Files() -> @b: Files.Files() -> {
    prev == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
) -> {
  RContents.Content.apply.few(
    ws,
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
      wo => wb => hr => hc => {==}
    case Spec.Request.Write{b, q, w}:
      wo => wb => hr => hc => {==}
    case Spec.Request.Merge{f, x}:
      wo => wb => hr => hc => Few.of(ws, fits, prev, other, base)(wo)(wb)(hr)(hc)
    case Spec.Request.Resolve{m, q, w}:
      wo => wb => hr => hc => {==}
    case Spec.Request.Mark{b, m, v}:
      wo => wb => hr => hc => {==}
    case Spec.Request.Move{b, t, v}:
      wo => wb => hr => hc => {==}
    case Spec.Request.Group{h, g, ms}:
      wo => wb => hr => hc => {==}
    case Spec.Request.Own{c, g}:
      wo => wb => hr => hc => {==}

# a version that reads only the paths of the writes h, if known, has the
# content that it has when it reads every path: when other is base with the
# writes, and prev is clean
def Few.next(
  h: Maybe<&2, List<&2, RContents.Write>>,
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(prev) == True{}: Bool
} -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @ws: List<
    &2,
    RContents.Write> -> @t: Files.Files() -> @b: Files.Files() -> {
    h == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
  } -> {
    other == Some{t}: Maybe<&2, Files.Files()>
  } -> {base == Some{b}: Maybe<&2, Files.Files()>} -> {t == Writes.apply(ws, b): Files.Files()}
) -> (
  @ws: List<
    &2,
    RContents.Write> -> @o: Files.Files() -> @b: Files.Files() -> {
    h == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
  } -> {
    prev == Some{o}: Maybe<&2, Files.Files()>
  } -> {
    base == Some{b}: Maybe<&2, Files.Files()>
  } -> {
    Clean.all(
      o,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Writes.apply(ws, b))
      )
    )
      == True{}: Bool
  }
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
      wo => wb => hr => hc => {==}
    case Some{ws} None{}:
      wo => wb => hr => hc => {==}
    case Some{+ws} Some{e}:
      wo => wb => hr => hc => Few.apply(
        ws,
        RLines.Ask.request(RLines.Entry.ask(e)),
        fits,
        prev,
        other,
        base
      )(
        wo
      )(
        wb
      )(
        t => b => et => eb => hr(ws)(t)(b)({==})(et)(eb)
      )(o => b => ep => eb => hc(ws)(o)(b)({==})(ep)(eb))

# Small laws for the hint of a merge
# ----------------------------------

# a number less another, plus the other, is the number, when the other is
# not greater
def Nat.sub_add(
  a: Nat,
  b: Nat
) -> {Nat.is_le(b, a) == True{}: Bool} -> {Nat.add(Nat.sub(a, b), b) == a: Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+bp:
      h => Empty.absurd({Nat.add(0n, 1n+bp) == 0n: Nat}, Shared.Bool.false_ne_true(h))
    case 1n+ap 0n:
      h => Equal.cong(Nat, Nat, z => 1n+z, Nat.add(ap, 0n), ap, Shared.Nat.add_zero(ap))
    case 1n+(+ap) 1n+(+bp):
      h =>
        %Equal.sym(
          Nat,
          Nat.add(Nat.sub(ap, bp), 1n+bp),
          1n+Nat.add(Nat.sub(ap, bp), bp),
          Shared.Nat.add_succ(Nat.sub(ap, bp), bp)
        ): {_ == 1n+ap: Nat}
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(ap, bp), bp), ap, Nat.sub_add(ap, bp)(h))

# a "when" that gives something has a test that holds
def When.cond(
  -B: Data,
  c: Bool,
  -k: Unit -> Maybe<&2, B>,
  -y: B
) -> {Shared.Maybe.when(B, c, k) == Some{y}: Maybe<&2, B>} -> {c == True{}: Bool}:
  match c:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(B, y, h))

# a "when" that gives something gives what its branch gives
def When.then(
  -B: Data,
  c: Bool,
  -k: Unit -> Maybe<&2, B>,
  -y: B
) -> {Shared.Maybe.when(B, c, k) == Some{y}: Maybe<&2, B>} -> {k(Unit{}) == Some{y}: Maybe<&2, B>}:
  match c:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({k(Unit{}) == Some{y}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, y, h))

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

# the clashes among the paths ps are the paths of ps among the clashes of
# the paths of the writes ws, when theirs is the base with the writes
def Clash.among(
  ps: List<&2, String>,
  +b: Files.Files(),
  +o: Files.Files(),
  +ws: List<&2, RContents.Write>,
  +wb: {FileLaws.Files.wf(b) == True{}: Bool}
) -> {
  RContents.Merge.clashes.go(
    b,
    o,
    Writes.apply(ws, b),
    ps
  )
    == RContents.Paths.among(
      ps,
      RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws))
    ): List<&2, String>
}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      Reads.Eq.back(
        Bool,
        d => {
          List.filter.put(
            String,
            p,
            RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), rest),
            d
          )
            == List.filter.put(
              String,
              p,
              RContents.Paths.among(
                rest,
                RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws))
              ),
              List.contains(
                ~String,
                ~String.eq,
                RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws)),
                p
              )
            ): List<&2, String>
        },
        Maybe.is_none(
          &2,
          Maybe<&2, List<&2, U32>>,
          RContents.Merge.at(b, o, Writes.apply(ws, b), p)
        ),
        List.contains(
          ~String,
          ~String.eq,
          RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws)),
          p
        ),
        Clash.same(
          b,
          o,
          Writes.apply(ws, b),
          RContents.Writes.paths(ws),
          p,
          ho => Writes.apply_other(ws, b, p)(wb)(ho)
        ),
        Equal.cong(
          List<&2, String>,
          List<&2, String>,
          l => List.filter.put(
            String,
            p,
            l,
            List.contains(
              ~String,
              ~String.eq,
              RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws)),
              p
            )
          ),
          RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), rest),
          RContents.Paths.among(
            rest,
            RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws))
          ),
          Clash.among(rest, b, o, ws, wb)
        )
      )

# the clashes of a merge that reads the paths of the writes ws are the
# clashes of the merge of every path, when theirs is the base with the writes
def Few.clashes(
  +b: Files.Files(),
  +o: Files.Files(),
  +ws: List<&2, RContents.Write>,
  wb: {FileLaws.Files.wf(b) == True{}: Bool}
) -> {
  RContents.Merge.clashes.few(
    b,
    o,
    Writes.apply(ws, b),
    ws
  )
    == RContents.Merge.clashes(b, o, Writes.apply(ws, b)): List<&2, String>
}:
  Equal.trans(
    List<&2, String>,
    RContents.Merge.clashes.few(b, o, Writes.apply(ws, b), ws),
    RContents.Paths.among(
      RContents.Merge.paths(b, o, Writes.apply(ws, b)),
      RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws))
    ),
    RContents.Merge.clashes(b, o, Writes.apply(ws, b)),
    Among.few(
      RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws)),
      RContents.Merge.paths(b, o, Writes.apply(ws, b))
    ),
    Equal.sym(
      List<&2, String>,
      RContents.Merge.clashes(b, o, Writes.apply(ws, b)),
      RContents.Paths.among(
        RContents.Merge.paths(b, o, Writes.apply(ws, b)),
        RContents.Merge.clashes.go(b, o, Writes.apply(ws, b), RContents.Writes.paths(ws))
      ),
      Clash.among(RContents.Merge.paths(b, o, Writes.apply(ws, b)), b, o, ws, wb)
    )
  )

# the clashes of a merge that fits, read from the paths of the writes ws,
# are those read from every path, when theirs is base with the writes
def Few.clashes_few(
  +ws: List<&2, RContents.Write>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @t: Files.Files() -> @b: Files.Files() -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {base == Some{b}: Maybe<&2, Files.Files()>} -> {t == Writes.apply(ws, b): Files.Files()}
) -> {
  RAnswers.Clashes.at.few(
    ws,
    fits,
    base,
    ours,
    theirs
  )
    == RAnswers.Clashes.at(fits, base, ours, theirs): Maybe<&2, List<&2, String>>
}:
  match fits base ours theirs:
    case True{} Some{+b} Some{+o} Some{+t}:
      wb => hr => Reads.Eq.back(
        Files.Files(),
        y => {
          Some{
            RContents.Merge.clashes.few(b, o, y, ws)
          }
            == Some{RContents.Merge.clashes(b, o, y)}: Maybe<&2, List<&2, String>>
        },
        t,
        Writes.apply(ws, b),
        hr(t)(b)({==})({==}),
        Equal.cong(
          List<&2, String>,
          Maybe<&2, List<&2, String>>,
          z => Some{z},
          RContents.Merge.clashes.few(b, o, Writes.apply(ws, b), ws),
          RContents.Merge.clashes(b, o, Writes.apply(ws, b)),
          Few.clashes(b, o, ws, wb)
        )
      )
    case True{} Some{b} Some{o} None{}:
      wb => hr => {==}
    case True{} Some{b} None{} theirs:
      wb => hr => {==}
    case True{} None{} ours theirs:
      wb => hr => {==}
    case False{} base ours theirs:
      wb => hr => {==}

# the clashes of a merge, read from the paths of the writes h, if known, are
# those read from every path, when theirs is base with the writes
def Few.clashes_at(
  h: Maybe<&2, List<&2, RContents.Write>>,
  fits: Bool,
  base: Maybe<&2, Files.Files()>,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>
) -> {
  Contents.Content.sound(base) == True{}: Bool
} -> (
  @ws: List<
    &2,
    RContents.Write> -> @t: Files.Files() -> @b: Files.Files() -> {
    h == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
  } -> {
    theirs == Some{t}: Maybe<&2, Files.Files()>
  } -> {base == Some{b}: Maybe<&2, Files.Files()>} -> {t == Writes.apply(ws, b): Files.Files()}
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
      wb => hr => {==}
    case Some{+ws}:
      wb => hr => Few.clashes_few(
        ws,
        fits,
        base,
        ours,
        theirs
      )(wb)(t => b => et => eb => hr(ws)(t)(b)({==})(et)(eb))
