import Base
import ../history/spec.bend as History
import ../shared.bend as Shared
import ./spec.bend as Spec

# l with x as the one head of the path p
def Line.set(l: Spec.Line, p: String, x: Shared.Bytes()) -> Spec.Line:
  match l:
    case Spec.Line{sp, nm, hs}:
      Spec.Line{sp, nm, Shared.Table.set(List<&2, Shared.Bytes()>, hs, p, [x])}

def Spec.Line.advance(l, h, n, expect, x):
  +l = l
  +n = n
  +x = x
  +expect = expect
  +now = Spec.Line.heads(l, n)
  ok = List.all.if(u => Spec.Line.fits(h, n, expect, x), History.Ids.is_eq(expect, now))
  Shared.Bool.when(
    Result<&2, &2, Spec.Refused, Spec.Line>,
    ok,
    u => Done{Line.set(l, Shared.Name.path(n), x)},
    u => Fail{Spec.Refused{now}}
  )

def advance_refused.i1(
  l: Spec.Line,
  h: History.History,
  n: Shared.Name,
  expect: List<&2, Shared.Bytes()>,
  x: Shared.Bytes(),
  +g: Bool,
  +g1: Bool,
  hg: {g1 == Spec.Line.fits.of(History.History.get(h, x), n, expect): Bool}
) -> {
  Bool.not(
    Result.is_done(
      &2,
      &2,
      Spec.Refused,
      Spec.Line,
      Shared.Bool.when(
        Result<&2, &2, Spec.Refused, Spec.Line>,
        List.all.if(u => Spec.Line.fits(h, n, expect, x), g),
        u => Done{Line.set(l, Shared.Name.path(n), x)},
        u => Fail{Spec.Refused{Spec.Line.heads(l, n)}}
      )
    )
  )
    == Bool.not(Bool.and(g, g1)): Bool
}:
  match g:
    case False{}:
      {==}
    case True{}:
      match g1:
        case False{}:
          %hg:
            {
              Bool.not(
                Result.is_done(
                  &2,
                  &2,
                  Spec.Refused,
                  Spec.Line,
                  Shared.Bool.when(
                    Result<&2, &2, Spec.Refused, Spec.Line>,
                    _,
                    u => Done{Line.set(l, Shared.Name.path(n), x)},
                    u => Fail{Spec.Refused{Spec.Line.heads(l, n)}}
                  )
                )
              )
                == True{}: Bool
            }
          {==}
        case True{}:
          %hg:
            {
              Bool.not(
                Result.is_done(
                  &2,
                  &2,
                  Spec.Refused,
                  Spec.Line,
                  Shared.Bool.when(
                    Result<&2, &2, Spec.Refused, Spec.Line>,
                    _,
                    u => Done{Line.set(l, Shared.Name.path(n), x)},
                    u => Fail{Spec.Refused{Spec.Line.heads(l, n)}}
                  )
                )
              )
                == False{}: Bool
            }
          {==}

def Spec.advance_refused(l, h, n, expect, x):
  +l = l
  +h = h
  +n = n
  +expect = expect
  +x = x
  advance_refused.i1(
    l,
    h,
    n,
    expect,
    x,
    History.Ids.is_eq(expect, Spec.Line.heads(l, n)),
    Spec.Line.fits.of(History.History.get(h, x), n, expect),
    {==}
  )
