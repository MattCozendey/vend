import Base
import ../shared/shared/ledger.bend as Ledgers
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./shared/format.bend as Formats
import ./spec.bend as Spec

# The helpers of the laws of the spec, said of the facts of a node
# ----------------------------------------------------------------
# Each def here is the def of the same name of spec.bend, with the facts s in
# place of the node: its answers are Answers.Answer.of, its reads
# Contents.Content.read. The laws of the core are stated with them; impl.bend
# turns them into the laws of the spec.

# the versions ps that a version made by the request r, after version k of c,
# comes from: version k, and the version that a merge or a move takes
def Request.Parents(r: Spec.Request, c: Ledgers.Line, k: Nat, ps: List<&2, Spec.Point>) -> Type:
  match r:
    case Spec.Request.Merge{f, x}:
      Exists(Nat, v => {ps == [Spec.Point{c, k}, Spec.Point{f, v}]: List<&2, Spec.Point>})
    case Spec.Request.Move{b, t, v}:
      {ps == [Spec.Point{c, k}, Spec.Point{t, v}]: List<&2, Spec.Point>}
    case _:
      {ps == [Spec.Point{c, k}]: List<&2, Spec.Point>}

# qs is a chain of parents from the version c, k back to a
def Back(
  s: Facts.Facts(),
  a: Spec.Point,
  qs: List<&2, Spec.Point>,
  c: Ledgers.Line,
  k: Nat
) -> Type:
  match qs:
    case Nil{}:
      {a == Spec.Point{c, k}: Spec.Point}
    case Con{q, rest}:
      Exists(
        List<&2, Spec.Point>,
        ps => {
          Answers.Answer.of(
            s,
            Spec.Question.Parents{c, k}
          )
            == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
        }
          & (
            {
              List.contains(~Spec.Point, ~Spec.Point.is_eq, ps, q) == True{}: Bool
            }
              & Back(s, a, rest, Spec.Point.line(q), Spec.Point.n(q))
          )
      )

# the version a is the version c, k or one that it comes from
def Before(s: Facts.Facts(), a: Spec.Point, c: Ledgers.Line, k: Nat) -> Type:
  Exists(List<&2, Spec.Point>, qs => Back(s, a, qs, c, k))

# version k of c is the decision of the request i, which asked for r
def Made(s: Facts.Facts(), c: Ledgers.Line, k: Nat, i: Ledgers.Id, r: Spec.Request) -> Type:
  {
    Answers.Answer.of(
      s,
      Spec.Question.Version{c, k}
    )
      == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
  }
    & {
      Answers.Answer.of(
        s,
        Spec.Question.Request{c, i}
      )
        == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
    }

# version j of the store of c is the latest that decides r among those up to m
def Latest(s: Facts.Facts(), c: Ledgers.Line, j: Nat, m: Nat, r: Spec.Request) -> Type:
  Exists(
    Ledgers.Id,
    i => Made(s, Ledgers.Line{Spec.Line.store(c), None{}}, j, i, r)
  )
    & {Nat.is_le(j, m) == True{}: Bool}

# ps is a chain of imports from a to b, in version k of the line c at n, in
# the build of the conditions bs
def Imports(
  s: Facts.Facts(),
  c: Ledgers.Line,
  k: Nat,
  bs: List<&2, String>,
  a: String,
  ps: List<&2, String>,
  b: String
) -> Type:
  match ps:
    case Nil{}:
      {a == b: String}
    case Con{q, rest}:
      Exists(
        List<&2, U32>,
        ws => {
          Contents.Content.read(s, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          & (
            {
              List.contains(
                ~String,
                ~String.eq,
                Formats.Format.imports(a, ws, bs),
                q
              )
                == True{}: Bool
            }
              & Imports(s, c, k, bs, q, rest, b)
          )
      )

# the path p is reached from one of the paths us through imports
def Reaches(
  s: Facts.Facts(),
  c: Ledgers.Line,
  k: Nat,
  bs: List<&2, String>,
  us: List<&2, String>,
  p: String
) -> Type:
  Exists(
    String,
    u => {
      List.contains(~String, ~String.eq, us, u) == True{}: Bool
    }
      & Exists(List<&2, String>, ps => Imports(s, c, k, bs, u, ps, p))
  )

# the resource at p differs from version a to version b of c at n
def Changed(s: Facts.Facts(), c: Ledgers.Line, a: Nat, b: Nat, p: String) -> Type:
  Exists(
    Maybe<&2, List<&2, U32>>,
    x => Exists(
      Maybe<&2, List<&2, U32>>,
      y => {
        Contents.Content.read(s, c, a, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
        & (
          {
            Contents.Content.read(s, c, b, p) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
            & ({x == y: Maybe<&2, List<&2, U32>>} -> Empty)
        )
    )
  )
