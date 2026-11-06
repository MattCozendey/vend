import Base
import ../history/spec.bend as History
import ../shared.bend as Shared
import ./spec.bend as Spec

# l with x as the one head of the path p
def Line.set(l: Spec.Line, p: String, x: Shared.Bytes()) -> Spec.Line:
  match l:
    case Spec.Line{sp, nm, hs}:
      Spec.Line{sp, nm, Map.set(&2, List<&2, Shared.Bytes()>, hs, p, [x])}

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
