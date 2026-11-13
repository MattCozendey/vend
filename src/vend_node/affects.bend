import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./mirror.bend as Mirror
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as Files
import ./shared/files.bend as FileLaws
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec

# What a writer is told: the laws
# -------------------------------
# The reply to Affects is the paths that us reaches in the newer content, or
# that are among us, whose words differ in the two contents. The reached paths
# are a closure in the graph of the imports (groups.bend, Closure): it holds
# only paths reached from us (affects_only), and each of them (affects_all).

# Members
# -------

# the path x is among xs
def In(xs: List<&2, String>, x: String) -> Data:
  {List.contains(~String, ~String.eq, xs, x) == True{}: Bool}

# a list holds its first path
def In.head(h: String, -t: List<&2, String>) -> In(h <> t, h):
  Lists.List.contains_head(~String, ~String.eq, ~Texts.String.laws(), h, t)

# a member of t is a member of h <> t
def In.tail(h: String, t: List<&2, String>, x: String) -> In(t, x) -> In(h <> t, x):
  Shared.List.contains_cons(~String, ~String.eq, h, t, x)

# a member of h <> t is h or a member of t: what follows from each follows
def In.cases(
  -P: Type,
  +h: String,
  -t: List<&2, String>,
  +x: String,
  hin: In(h <> t, x),
  a: {h == x: String} -> P,
  b: In(t, x) -> P
) -> P:
  Lists.List.contains_cons_by(~String, ~String.eq, ~Texts.String.laws(), P, h, t, x, hin, a, b)

# the empty list has no member
def In.nil(-P: Type, -x: String, h: In([], x)) -> P:
  Empty.absurd(P, Shared.Bool.false_ne_true(h))

# a member of xs is a member of the equal list ys
def In.cast(
  -xs: List<&2, String>,
  -ys: List<&2, String>,
  -x: String,
  e: {xs == ys: List<&2, String>},
  h: In(xs, x)
) -> In(ys, x):
  %e: In(_, x)
  h

# each member of ps is a member of ks when ps is within ks
def In.within(
  ps: List<&2, String>,
  +ks: List<&2, String>,
  +x: String
) -> {Shared.List.within(~String, ~String.eq, ps, ks) == True{}: Bool} -> In(ps, x) -> In(ks, x):
  match ps:
    case Nil{}:
      hw => h => In.nil(In(ks, x), x, h)
    case Con{+p, +r}:
      +hw => h => In.cases(In(ks, x), p, r, x, h, e => (
          %e: In(ks, _)
          Shared.Bool.and_true_left(List.contains(~String, ~String.eq, ks, p), Shared.List.within(~String, ~String.eq, r, ks))(hw)), t => In.within(r, ks, x)(Shared.Bool.and_true_right(List.contains(~String, ~String.eq, ks, p), Shared.List.within(~String, ~String.eq, r, ks))(hw))(t))

# Reads and imports
# -----------------

# a read of a version whose content is b is a read of b
def Content.read_of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +b: Files.Files(),
  +p: String
) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(
    s,
    c,
    k,
    p
  )
    == Some{Files.Files.get(b, p)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  hb => Equal.cong(
    Maybe<&2, Files.Files()>,
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    m => RContents.Content.get(m, p),
    Contents.Content.of(s, c, k),
    Some{b},
    hb
  )

# the words that a read of a version gives are those of its content b
def Content.read_get(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +b: Files.Files(),
  +p: String,
  +x: Maybe<&2, List<&2, U32>>
) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(s, c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Files.Files.get(b, p) == x: Maybe<&2, List<&2, U32>>}:
  hb => er => Shared.Maybe.some_inj(
    Maybe<&2, List<&2, U32>>,
    Files.Files.get(b, p),
    x,
    Equal.trans(
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      Some{Files.Files.get(b, p)},
      Contents.Content.read(s, c, k, p),
      Some{x},
      Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Contents.Content.read(s, c, k, p),
        Some{Files.Files.get(b, p)},
        Content.read_of(s, c, k, b, p)(hb)
      ),
      er
    )
  )

# an import of the words m at p, if any, is an import of words that m holds
def Reach.imports.of_in(
  m: Maybe<&2, List<&2, U32>>,
  +p: String,
  +bs: List<&2, String>,
  +x: String
) -> In(
  RAnswers.Reach.imports.of(p, bs, m),
  x
) -> Exists(
  List<&2, U32>,
  ws => {m == Some{ws}: Maybe<&2, List<&2, U32>>} & In(Formats.Format.imports(p, ws, bs), x)
):
  match m:
    case None{}:
      h => In.nil(
        Exists(
          List<&2, U32>,
          ws => {
            None{} == Some{ws}: Maybe<&2, List<&2, U32>>
          }
            & In(Formats.Format.imports(p, ws, bs), x)
        ),
        x,
        h
      )
    case Some{ws}:
      h => (ws, ({==}, h))

# Imports.step, once the words of p are known
def Imports.step.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +p: String,
  +q: String,
  +rest: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  ch: Mirror.Imports(s, c, k, bs, q, rest, x),
  w: Exists(
    List<&2, U32>,
    ws => {
      Files.Files.get(b, p) == Some{ws}: Maybe<&2, List<&2, U32>>
    }
      & In(Formats.Format.imports(p, ws, bs), q)
  )
) -> Mirror.Imports(s, c, k, bs, p, q <> rest, x):
  (+ws, w2) = w
  (e, hi) = w2
  (ws, ((
        %e: {Contents.Content.read(s, c, k, p) == Some{_}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
        Content.read_of(s, c, k, b, p)(hb)), (hi, ch)))

# a chain of imports from q, after an import q of p in the content b of the
# version, is a chain from p
def Imports.step(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +p: String,
  +q: String,
  +rest: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  hi: In(RAnswers.Reach.imports(b, bs, p), q),
  ch: Mirror.Imports(s, c, k, bs, q, rest, x)
) -> Mirror.Imports(s, c, k, bs, p, q <> rest, x):
  Imports.step.of(
    s,
    c,
    k,
    bs,
    b,
    p,
    q,
    rest,
    x,
    hb,
    ch,
    Reach.imports.of_in(Files.Files.get(b, p), p, bs, q)(hi)
  )

# the path q is an import of a in the content b, as a step of a chain says
def Reach.imports_of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +q: String,
  +ws: List<&2, U32>
) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(s, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> In(Formats.Format.imports(a, ws, bs), q) -> In(RAnswers.Reach.imports(b, bs, a), q):
  hb => er => hi =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Files.Files.get(b, a),
      Some{ws},
      Content.read_get(s, c, k, b, a, Some{ws})(hb)(er)
    ): In(RAnswers.Reach.imports.of(a, bs, _), q)
    hi

# The graph of the imports
# ------------------------

# Reached.live, by whether p holds words (hit)
def Reached.live.at(
  hit: Bool,
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +q: String
) -> {
  List.contains(~String, ~String.eq, RAnswers.Reached.succ.if(hit, b, bs, p), q) == True{}: Bool
} -> {hit == True{}: Bool}:
  match hit:
    case False{}:
      h => h
    case True{}:
      h => {==}

# Reached.live, for a content b and the paths ps
def Reached.live.of(
  +b: Files.Files(),
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  +q: String
) -> {
  List.contains(~String, ~String.eq, RAnswers.Reached.succ.of(b, bs, ps, p), q) == True{}: Bool
} -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}:
  h => Reached.live.at(List.contains(~String, ~String.eq, ps, p), b, bs, p, q)(h)

# a path that leads to another is a node of the graph
def Reached.live(
  g: RAnswers.Reached,
  p: String,
  q: String
) -> {
  List.contains(~String, ~String.eq, RAnswers.Reached.succ(g, p), q) == True{}: Bool
} -> {List.contains(~String, ~String.eq, RAnswers.Reached.nodes(g), p) == True{}: Bool}:
  match g:
    case RAnswers.Reached{b, bs, ps}:
      h => Reached.live.of(b, bs, ps, p, q)(h)

# Reached.succ_imports, by whether p holds words (hit)
def Reached.succ_imports.at(
  hit: Bool,
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +q: String
) -> In(RAnswers.Reached.succ.if(hit, b, bs, p), q) -> In(RAnswers.Reach.imports(b, bs, p), q):
  match hit:
    case False{}:
      h => In.nil(In(RAnswers.Reach.imports(b, bs, p), q), q, h)
    case True{}:
      h => h

# a path that p leads to in the graph of the content b is an import of p
def Reached.succ_imports(
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +q: String
) -> In(
  RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, p),
  q
) -> In(RAnswers.Reach.imports(b, bs, p), q):
  h => Reached.succ_imports.at(
    List.contains(~String, ~String.eq, Files.Files.paths(b), p),
    b,
    bs,
    p,
    q
  )(h)

# Reached.imports_succ, once the words of p are known
def Reached.imports_succ.of(
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +q: String,
  hw: {FileLaws.Files.wf(b) == True{}: Bool},
  hi: In(RAnswers.Reach.imports(b, bs, p), q),
  w: Exists(
    List<&2, U32>,
    ws => {
      Files.Files.get(b, p) == Some{ws}: Maybe<&2, List<&2, U32>>
    }
      & In(Formats.Format.imports(p, ws, bs), q)
  )
) -> In(RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, p), q):
  (+ws, w2) = w
  (e, hi2) = w2
  %Equal.sym(
    Bool,
    List.contains(~String, ~String.eq, Files.Files.paths(b), p),
    True{},
    FileLaws.Files.get_paths(b, p, ws)(hw)(e)
  ): In(RAnswers.Reached.succ.if(_, b, bs, p), q)
  hi

# an import of p in a content b that is well formed is a path that p leads to
# in the graph of b
def Reached.imports_succ(
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +q: String
) -> In(
  RAnswers.Reach.imports(b, bs, p),
  q
) -> {
  FileLaws.Files.wf(b) == True{}: Bool
} -> In(RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, p), q):
  +hi => hw => Reached.imports_succ.of(
    b,
    bs,
    p,
    q,
    hw,
    hi,
    Reach.imports.of_in(Files.Files.get(b, p), p, bs, q)(hi)
  )

# Each reached path is reached
# ----------------------------

# Reach.path_chain, once the chain from q to x is found
def Reach.path_chain.cons(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +q: String,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  hi: In(RAnswers.Reach.imports(b, bs, a), q),
  w: Exists(List<&2, String>, qs => Mirror.Imports(s, c, k, bs, q, qs, x))
) -> Exists(List<&2, String>, qs => Mirror.Imports(s, c, k, bs, a, qs, x)):
  (+qs, ch) = w
  (q <> qs, Imports.step(s, c, k, bs, b, a, q, qs, x, hb, hi, ch))

# a path of the graph from what a leads to, to x, is a chain of imports from a
# to x, in a version whose content is b
def Reach.path_chain(
  r: List<&2, String>,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +x: String,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> {
  Reaches.Reach.path(
    ~String,
    ~RAnswers.Reached,
    ~String.eq,
    ~RAnswers.Reached.succ,
    r,
    RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
    RAnswers.Reached{b, bs, Files.Files.paths(b)},
    x
  )
    == True{}: Bool
} -> Exists(List<&2, String>, qs => Mirror.Imports(s, c, k, bs, a, qs, x)):
  match r:
    case Nil{}:
      h => (
        [x],
        Imports.step(s, c, k, bs, b, a, x, [], x, hb, Reached.succ_imports(b, bs, a, x)(h), {==})
      )
    case Con{+q, +t}:
      +h => Reach.path_chain.cons(
        s,
        c,
        k,
        bs,
        b,
        a,
        q,
        x,
        hb,
        Reached.succ_imports(
          b,
          bs,
          a,
          q
        )(
          Shared.Bool.and_true_left(
            List.contains(
              ~String,
              ~String.eq,
              RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
              q
            ),
            Reaches.Reach.path(
              ~String,
              ~RAnswers.Reached,
              ~String.eq,
              ~RAnswers.Reached.succ,
              t,
              RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, q),
              RAnswers.Reached{b, bs, Files.Files.paths(b)},
              x
            )
          )(h)
        ),
        Reach.path_chain(
          t,
          s,
          c,
          k,
          bs,
          b,
          q,
          x,
          hb
        )(
          Shared.Bool.and_true_right(
            List.contains(
              ~String,
              ~String.eq,
              RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
              q
            ),
            Reaches.Reach.path(
              ~String,
              ~RAnswers.Reached,
              ~String.eq,
              ~RAnswers.Reached.succ,
              t,
              RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, q),
              RAnswers.Reached{b, bs, Files.Files.paths(b)},
              x
            )
          )(h)
        )
      )

# Reach.of_reaches, by the path ps of the graph from us to x
def Reach.of_reaches.by(
  ps: List<&2, String>,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +x: String,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  +hp: {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      ps,
      us,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }
) -> Mirror.Reaches(s, c, k, bs, us, x):
  match ps:
    case Nil{}:
      (x, (hp, ([], {==})))
    case Con{+p, +r}:
      (
        p,
        (
          Shared.Bool.and_true_left(
            List.contains(~String, ~String.eq, us, p),
            Reaches.Reach.path(
              ~String,
              ~RAnswers.Reached,
              ~String.eq,
              ~RAnswers.Reached.succ,
              r,
              RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, p),
              RAnswers.Reached{b, bs, Files.Files.paths(b)},
              x
            )
          )(hp),
          Reach.path_chain(
            r,
            s,
            c,
            k,
            bs,
            b,
            p,
            x,
            hb
          )(
            Shared.Bool.and_true_right(
              List.contains(~String, ~String.eq, us, p),
              Reaches.Reach.path(
                ~String,
                ~RAnswers.Reached,
                ~String.eq,
                ~RAnswers.Reached.succ,
                r,
                RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, p),
                RAnswers.Reached{b, bs, Files.Files.paths(b)},
                x
              )
            )(hp)
          )
        )
      )

# Reach.of_reaches, once the path of the graph from us to x is found
def Reach.of_reaches.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  w: &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      ps,
      us,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }
) -> Mirror.Reaches(s, c, k, bs, us, x):
  match w:
    case (ps, hp):
      Reach.of_reaches.by(ps, s, c, k, bs, b, us, x, hb, hp)

# each path that Reach.of answers is reached from us, in a version whose
# content is b
def Reach.of_reaches(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> In(RAnswers.Reach.of(b, bs, us), x) -> Mirror.Reaches(s, c, k, bs, us, x):
  h => Reach.of_reaches.of(
    s,
    c,
    k,
    bs,
    b,
    us,
    x,
    hb,
    Groups.Closure.of_path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      ~RAnswers.Reached.nodes,
      ~Texts.String.laws(),
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      us,
      x
    )(h)
  )

# Each reached path is answered
# -----------------------------

# Reach.chain_path, once the path of the graph from what a leads to is found
def Reach.chain_path.cons(
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +x: String,
  +lv: List<&2, String>,
  ha: In(lv, a),
  w: &qs: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      qs,
      RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }
) -> &qs:
  List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      qs,
      lv,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }:
  match w:
    case (+qs, hp):
      (
        a <> qs,
        Shared.Bool.and_both(
          List.contains(~String, ~String.eq, lv, a),
          Reaches.Reach.path(
            ~String,
            ~RAnswers.Reached,
            ~String.eq,
            ~RAnswers.Reached.succ,
            qs,
            RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
            RAnswers.Reached{b, bs, Files.Files.paths(b)},
            x
          )
        )(ha)(hp)
      )

# Reach.chain_path at a step of the chain w, given the rest of the chain (ih)
def Reach.chain_path.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +q: String,
  -rest: List<&2, String>,
  +x: String,
  +lv: List<&2, String>,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  ih: Mirror.Imports(
    s,
    c,
    k,
    bs,
    q,
    rest,
    x
  ) -> In(
    RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
    q
  ) -> &qs: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      qs,
      RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  },
  ha: In(lv, a),
  w: Exists(
    List<&2, U32>,
    ws => {
      Contents.Content.read(s, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
      & (In(Formats.Format.imports(a, ws, bs), q) & Mirror.Imports(s, c, k, bs, q, rest, x))
  )
) -> &qs:
  List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      qs,
      lv,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }:
  (+ws, w1) = w
  (er, w2) = w1
  (hi, ch2) = w2
  Reach.chain_path.cons(
    bs,
    b,
    a,
    x,
    lv,
    ha,
    ih(
      ch2
    )(
      Reached.imports_succ(
        b,
        bs,
        a,
        q
      )(
        Reach.imports_of(s, c, k, bs, b, a, q, ws)(hb)(er)(hi)
      )(Contents.Content.of_wf(s, c, k, b)(hb))
    )
  )

# a chain of imports from a path a of the level lv, to x, is a path of the
# graph from lv to x, in a version whose content is b
def Reach.chain_path(
  ps: List<&2, String>,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +a: String,
  +x: String,
  +lv: List<&2, String>,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> Mirror.Imports(s, c, k, bs, a, ps, x) -> In(lv, a) -> &qs:
  List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      qs,
      lv,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }:
  match ps:
    case Nil{}:
      ch => ha =>
        ([], (%ch: In(lv, _)
            ha))
    case Con{+q, rest}:
      ch => ha => Reach.chain_path.at(
        s,
        c,
        k,
        bs,
        b,
        a,
        q,
        rest,
        x,
        lv,
        hb,
        Reach.chain_path(
          rest,
          s,
          c,
          k,
          bs,
          b,
          q,
          x,
          RAnswers.Reached.succ(RAnswers.Reached{b, bs, Files.Files.paths(b)}, a),
          hb
        ),
        ha,
        ch
      )

# Reach.reaches_of, once the path of the graph from us to x is found
def Reach.reaches_of.of(
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +x: String,
  w: &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~RAnswers.Reached,
      ~String.eq,
      ~RAnswers.Reached.succ,
      ps,
      us,
      RAnswers.Reached{b, bs, Files.Files.paths(b)},
      x
    )
      == True{}: Bool
  }
) -> In(RAnswers.Reach.of(b, bs, us), x):
  match w:
    case (+ps, hp):
      Groups.Closure.path_of(
        ~String,
        ~RAnswers.Reached,
        ~String.eq,
        ~RAnswers.Reached.succ,
        ~RAnswers.Reached.nodes,
        ~Texts.String.laws(),
        ~Reached.live,
        RAnswers.Reached{b, bs, Files.Files.paths(b)},
        us,
        ps,
        x
      )(hp)

# the end of a chain of imports from one of us is a path that Reach.of
# answers, in a version whose content is b
def Reach.reaches_of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +u: String,
  +qs: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> In(us, u) -> Mirror.Imports(s, c, k, bs, u, qs, x) -> In(RAnswers.Reach.of(b, bs, us), x):
  hu => ch => Reach.reaches_of.of(
    bs,
    b,
    us,
    x,
    Reach.chain_path(qs, s, c, k, bs, b, u, x, us, hb)(ch)(hu)
  )

# ----------------------------

# a member of r is a member of r with h put, or not
def Delta.put_skip(
  keep: Bool,
  h: String,
  r: List<&2, String>,
  x: String
) -> In(r, x) -> In(List.filter.put(String, h, r, keep), x):
  match keep:
    case False{}:
      i => i
    case True{}:
      In.tail(h, r, x)

# the first path is among the changed ones when it differs
def Delta.changed_head(
  +g: RAnswers.Delta,
  +h: String,
  +rest: List<&2, String>
) -> {
  RAnswers.Delta.differ(g, h) == True{}: Bool
} -> In(
  List.filter.put(String, h, RAnswers.Delta.changed(g, rest), RAnswers.Delta.differ(g, h)),
  h
):
  d =>
    %Equal.sym(
      Bool,
      RAnswers.Delta.differ(g, h),
      True{},
      d
    ): In(List.filter.put(String, h, RAnswers.Delta.changed(g, rest), _), h)
    In.head(h, RAnswers.Delta.changed(g, rest))

# a path of ps that differs is among the changed ones
def Delta.changed_has(
  ps: List<&2, String>,
  +g: RAnswers.Delta,
  +p: String
) -> In(
  ps,
  p
) -> {RAnswers.Delta.differ(g, p) == True{}: Bool} -> In(RAnswers.Delta.changed(g, ps), p):
  match ps:
    case Nil{}:
      hin => d => In.nil(In([], p), p, hin)
    case Con{+h, +rest}:
      hin => In.cases(
        {
          RAnswers.Delta.differ(g, p) == True{}: Bool
        } -> In(
          List.filter.put(String, h, RAnswers.Delta.changed(g, rest), RAnswers.Delta.differ(g, h)),
          p
        ),
        h,
        rest,
        p,
        hin,
        e => (
          %e: {RAnswers.Delta.differ(g, _) == True{}: Bool} -> In(List.filter.put(String, h, RAnswers.Delta.changed(g, rest), RAnswers.Delta.differ(g, h)), _)
          Delta.changed_head(g, h, rest)),
        t => d => Delta.put_skip(
          RAnswers.Delta.differ(g, h),
          h,
          RAnswers.Delta.changed(g, rest),
          p
        )(Delta.changed_has(rest, g, p)(t)(d))
      )

# Delta.changed_in, from what the rest of the paths give
def Delta.changed_in.up(
  -g: RAnswers.Delta,
  h: String,
  rest: List<&2, String>,
  p: String,
  w: In(rest, p) & {RAnswers.Delta.differ(g, p) == True{}: Bool}
) -> In(h <> rest, p)
  & {RAnswers.Delta.differ(g, p) == True{}: Bool}:
  (a, d) = w
  (In.tail(h, rest, p)(a), d)

# a changed path is one of ps, and differs
def Delta.changed_in(
  ps: List<&2, String>,
  +g: RAnswers.Delta,
  +p: String
) -> In(
  RAnswers.Delta.changed(g, ps),
  p
) -> In(ps, p)
  & {RAnswers.Delta.differ(g, p) == True{}: Bool}:
  match ps:
    case Nil{}:
      hin => In.nil(In([], p) & {RAnswers.Delta.differ(g, p) == True{}: Bool}, p, hin)
    case Con{+h, +rest}:
      Lists.Bool.by(
        k => In(
          List.filter.put(String, h, RAnswers.Delta.changed(g, rest), k),
          p
        ) -> In(h <> rest, p)
          & {RAnswers.Delta.differ(g, p) == True{}: Bool},
        RAnswers.Delta.differ(g, h),
        e => hin => In.cases(
          In(h <> rest, p) & {RAnswers.Delta.differ(g, p) == True{}: Bool},
          h,
          RAnswers.Delta.changed(g, rest),
          p,
          hin,
          eq => (
            %eq: In(h <> rest, _) & {RAnswers.Delta.differ(g, _) == True{}: Bool}
            (In.head(h, rest), e)),
          t => Delta.changed_in.up(g, h, rest, p, Delta.changed_in(rest, g, p)(t))
        ),
        e => hin => Delta.changed_in.up(g, h, rest, p, Delta.changed_in(rest, g, p)(hin))
      )

# the words x, if any, are the same as the words y, if any
def Words.same(x: Maybe<&2, List<&2, U32>>, y: Maybe<&2, List<&2, U32>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, U32>, ~RFacts.Words.is_eq, x, y)

# words, if any, are the same as themselves
def Words.same_refl(x: Maybe<&2, List<&2, U32>>) -> {Words.same(x, x) == True{}: Bool}:
  match x:
    case None{}:
      {==}
    case Some{ws}:
      Facts.Words.is_eq_refl(ws)

# only equal words are the same
def Words.same_sound(
  x: Maybe<&2, List<&2, U32>>,
  y: Maybe<&2, List<&2, U32>>
) -> {Words.same(x, y) == True{}: Bool} -> {x == y: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~RFacts.Words.is_eq,
    a => b => Facts.Words.is_eq_sound(a, b),
    x,
    y
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# words do not differ from themselves
def Words.same_not(x: Maybe<&2, List<&2, U32>>) -> {Bool.not(Words.same(x, x)) == False{}: Bool}:
  %Equal.sym(Bool, Words.same(x, x), True{}, Words.same_refl(x)): {Bool.not(_) == False{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# equal words do not differ
def Words.differ_ne(
  +x: Maybe<&2, List<&2, U32>>,
  +y: Maybe<&2, List<&2, U32>>
) -> {x == y: Maybe<&2, List<&2, U32>>} -> {Bool.not(Words.same(x, y)) == True{}: Bool} -> Empty:
  e =>
    %e: {Bool.not(Words.same(x, _)) == True{}: Bool} -> Empty
    d => Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Bool.not(Words.same(x, x)),
        True{},
        Equal.sym(Bool, Bool.not(Words.same(x, x)), False{}, Words.same_not(x)),
        d
      )
    )

# words that are not equal differ
def Words.ne_differ(
  +x: Maybe<&2, List<&2, U32>>,
  +y: Maybe<&2, List<&2, U32>>
) -> ({x == y: Maybe<&2, List<&2, U32>>} -> Empty) -> {Bool.not(Words.same(x, y)) == True{}: Bool}:
  ne => Lists.Bool.by(
    k => {Bool.not(k) == True{}: Bool},
    Words.same(x, y),
    e => Empty.absurd({False{} == True{}: Bool}, ne(Words.same_sound(x, y)(e))),
    e => {==}
  )

# a path whose words differ in the contents fa and fb of two versions changed
# from one version to the other
def Changed.of_differ(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  d: {RAnswers.Delta.differ(RAnswers.Delta{fa, fb}, p) == True{}: Bool}
) -> Mirror.Changed(s, c, a, b, p):
  (
    Files.Files.get(fa, p),
    (
      Files.Files.get(fb, p),
      (
        Content.read_of(s, c, a, fa, p)(ea),
        (
          Content.read_of(s, c, b, fb, p)(eb),
          e => Words.differ_ne(Files.Files.get(fa, p), Files.Files.get(fb, p))(e)(d)
        )
      )
    )
  )

# Changed.differ, once the words x and y that the reads give are known
def Changed.differ.at(
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  -x: Maybe<&2, List<&2, U32>>,
  -y: Maybe<&2, List<&2, U32>>,
  ex: {Files.Files.get(fa, p) == x: Maybe<&2, List<&2, U32>>},
  ey: {Files.Files.get(fb, p) == y: Maybe<&2, List<&2, U32>>},
  ne: {x == y: Maybe<&2, List<&2, U32>>} -> Empty
) -> {RAnswers.Delta.differ(RAnswers.Delta{fa, fb}, p) == True{}: Bool}:
  Words.ne_differ(
    Files.Files.get(fa, p),
    Files.Files.get(fb, p)
  )(
    e => ne(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        x,
        Files.Files.get(fa, p),
        y,
        Equal.sym(Maybe<&2, List<&2, U32>>, Files.Files.get(fa, p), x, ex),
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Files.Files.get(fa, p),
          Files.Files.get(fb, p),
          y,
          e,
          ey
        )
      )
    )
  )

# the words of a path that changed from one version to another differ in
# their contents fa and fb
def Changed.differ(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  ch: Mirror.Changed(s, c, a, b, p)
) -> {RAnswers.Delta.differ(RAnswers.Delta{fa, fb}, p) == True{}: Bool}:
  (+x, w) = ch
  (+y, w2) = w
  (ra, w3) = w2
  (rb, ne) = w3
  Changed.differ.at(
    fa,
    fb,
    p,
    x,
    y,
    Content.read_get(s, c, a, fa, p, x)(ea)(ra),
    Content.read_get(s, c, b, fb, p, y)(eb)(rb),
    ne
  )

# What the reply says
# -------------------

# the names of a reply of names
def Reply.names(r: Spec.Reply) -> List<&2, String>:
  match r:
    case Spec.Reply.Names{ns}:
      ns
    case _:
      []

# what a reply of the names ps to Affects says, of the contents fa and fb
def Affects.Told(
  fa: Files.Files(),
  fb: Files.Files(),
  us: List<&2, String>,
  bs: List<&2, String>,
  ps: List<&2, String>
) -> Type:
  {
    RAnswers.Delta.changed(
      RAnswers.Delta{fa, fb},
      RAnswers.Reach.of(fb, bs, us)
    )
      == ps: List<&2, String>
  }

# what a reply of names to Affects says of the two contents old and new
def Affects.Some(
  old: Maybe<&2, Files.Files()>,
  new: Maybe<&2, Files.Files()>,
  us: List<&2, String>,
  bs: List<&2, String>,
  ps: List<&2, String>
) -> Type:
  Exists(
    Files.Files(),
    fa => Exists(
      Files.Files(),
      fb => {
        old == Some{fa}: Maybe<&2, Files.Files()>
      }
        & ({new == Some{fb}: Maybe<&2, Files.Files()>} & Affects.Told(fa, fb, us, bs, ps))
    )
  )

# a reply of names to Affects is given of two contents that the node holds
def Affects.of_some(
  old: Maybe<&2, Files.Files()>,
  new: Maybe<&2, Files.Files()>,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>
) -> {
  RAnswers.Affects.of(old, new, us, bs) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> Affects.Some(old, new, us, bs, ps):
  match old new:
    case Some{+fa} Some{+fb}:
      h => (
        fa,
        (
          fb,
          (
            {==},
            (
              {==},
              Equal.cong(
                Spec.Reply,
                List<&2, String>,
                r => Reply.names(r),
                Spec.Reply.Names{
                  RAnswers.Delta.changed(RAnswers.Delta{fa, fb}, RAnswers.Reach.of(fb, bs, us))
                },
                Spec.Reply.Names{ps},
                Shared.Maybe.some_inj(
                  Spec.Reply,
                  Spec.Reply.Names{
                    RAnswers.Delta.changed(RAnswers.Delta{fa, fb}, RAnswers.Reach.of(fb, bs, us))
                  },
                  Spec.Reply.Names{ps},
                  h
                )
              )
            )
          )
        )
      )
    case Some{fa} None{}:
      h => Empty.absurd(
        Affects.Some(Some{fa}, None{}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case None{} Some{fb}:
      h => Empty.absurd(
        Affects.Some(None{}, Some{fb}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case None{} None{}:
      h => Empty.absurd(
        Affects.Some(None{}, None{}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )

# The two laws
# ------------

# a member of the names ps of the reply is a reached path that differs
def Affects.told_in(
  +fa: Files.Files(),
  +fb: Files.Files(),
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  ep: {
    RAnswers.Delta.changed(
      RAnswers.Delta{fa, fb},
      RAnswers.Reach.of(fb, bs, us)
    )
      == ps: List<&2, String>
  },
  hin: In(ps, p)
) -> In(
  RAnswers.Reach.of(fb, bs, us),
  p
)
  & {RAnswers.Delta.differ(RAnswers.Delta{fa, fb}, p) == True{}: Bool}:
  Delta.changed_in(
    RAnswers.Reach.of(fb, bs, us),
    RAnswers.Delta{fa, fb},
    p
  )(
    In.cast(
      ps,
      RAnswers.Delta.changed(RAnswers.Delta{fa, fb}, RAnswers.Reach.of(fb, bs, us)),
      p,
      Equal.sym(
        List<&2, String>,
        RAnswers.Delta.changed(RAnswers.Delta{fa, fb}, RAnswers.Reach.of(fb, bs, us)),
        ps,
        ep
      ),
      hin
    )
  )

# Core.affects_only, once the contents are known and p is known to be reached
# and to differ
def Core.affects_only.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +p: String,
  +fa: Files.Files(),
  +fb: Files.Files(),
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  +eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  w: In(
    RAnswers.Reach.of(fb, bs, us),
    p
  )
    & {RAnswers.Delta.differ(RAnswers.Delta{fa, fb}, p) == True{}: Bool}
) -> Mirror.Changed(s, c, a, b, p)
  & Mirror.Reaches(s, c, b, bs, us, p):
  (hs, d) = w
  (
    Changed.of_differ(s, c, a, b, fa, fb, p, ea, eb, d),
    Reach.of_reaches(s, c, b, bs, fb, us, p, eb)(hs)
  )

# Core.affects_only, from what the reply says
def Core.affects_only.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  hin: In(ps, p),
  w: Affects.Some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)
) -> Mirror.Changed(s, c, a, b, p)
  & Mirror.Reaches(s, c, b, bs, us, p):
  (+fa, w1) = w
  (+fb, w2) = w1
  (ea, w3) = w2
  (eb, ep) = w3
  Core.affects_only.at(
    s,
    c,
    a,
    b,
    us,
    bs,
    p,
    fa,
    fb,
    ea,
    eb,
    Affects.told_in(fa, fb, us, bs, ps, p, ep, hin)
  )

# A writer is told only about changes to what its work uses.
def Core.affects_only(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Affects{c, a, b, us, bs}
  )
    == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> {
  List.contains(~String, ~String.eq, ps, p) == True{}: Bool
} -> Mirror.Changed(s, c, a, b, p)
  & Mirror.Reaches(s, c, b, bs, us, p):
  h => hin => Core.affects_only.of(
    s,
    c,
    a,
    b,
    us,
    bs,
    ps,
    p,
    hin,
    Affects.of_some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)(h)
  )

# Core.affects_all, once the path u that reaches p and its chain are known
def Core.affects_all.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +u: String,
  +qs: List<&2, String>,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  +eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  ep: {
    RAnswers.Delta.changed(
      RAnswers.Delta{fa, fb},
      RAnswers.Reach.of(fb, bs, us)
    )
      == ps: List<&2, String>
  },
  ch: Mirror.Changed(s, c, a, b, p),
  hu: In(us, u),
  chain: Mirror.Imports(s, c, b, bs, u, qs, p)
) -> In(ps, p):
  In.cast(
    RAnswers.Delta.changed(RAnswers.Delta{fa, fb}, RAnswers.Reach.of(fb, bs, us)),
    ps,
    p,
    ep,
    Delta.changed_has(
      RAnswers.Reach.of(fb, bs, us),
      RAnswers.Delta{fa, fb},
      p
    )(
      Reach.reaches_of(s, c, b, bs, fb, us, u, qs, p, eb)(hu)(chain)
    )(Changed.differ(s, c, a, b, fa, fb, p, ea, eb, ch))
  )

# Core.affects_all, from what the reply says
def Core.affects_all.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  w: Affects.Some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps),
  ch: Mirror.Changed(s, c, a, b, p),
  rc: Mirror.Reaches(s, c, b, bs, us, p)
) -> In(ps, p):
  (+fa, w1) = w
  (+fb, w2) = w1
  (ea, w3) = w2
  (eb, ep) = w3
  (+u, r1) = rc
  (hu, r2) = r1
  (+qs, chain) = r2
  Core.affects_all.at(s, c, a, b, us, bs, ps, p, fa, fb, u, qs, ea, eb, ep, ch, hu, chain)

# And it is told about each of them.
def Core.affects_all(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Affects{c, a, b, us, bs}
  )
    == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> Mirror.Changed(
  s,
  c,
  a,
  b,
  p
) -> Mirror.Reaches(
  s,
  c,
  b,
  bs,
  us,
  p
) -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}:
  h => ch => rc => Core.affects_all.of(
    s,
    c,
    a,
    b,
    us,
    bs,
    ps,
    p,
    Affects.of_some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)(h),
    ch,
    rc
  )
