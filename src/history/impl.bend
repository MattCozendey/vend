import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ./spec.bend as Spec

# A commit checks the heads it was given against the heads now, exactly
# and in order, and then makes its node the one head. History.join is not
# written yet.
def Spec.Ids.is_eq(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Spec.Ids.is_eq(xt, yt), Shared.Bytes.is_eq(x, y))
    case _ _:
      False{}

# h with node v under its id x, and x the one head of n
def History.put(h: Spec.History, n: Shared.Name, +x: Shared.Bytes(), v: Spec.Node) -> Spec.History:
  match h:
    case Spec.History{ns, hs}:
      nodes = Map.set(&2, Maybe<&2, Spec.Node>, ns, Hash.Hash.hex(x), Some{v})
      Spec.History{nodes, Map.set(&2, List<&2, Shared.Bytes()>, hs, Shared.Name.show(n), [x])}

# the commit of node v, once its parents are known to be the heads of n
def History.commit.of(
  h: Spec.History,
  n: Shared.Name,
  +v: Spec.Node
) -> Result<&2, &2, Spec.Refused, Spec.Committed>:
  +x = Spec.Node.id(v)
  Done{Spec.Committed{History.put(h, n, x, v), x}}

def Spec.History.commit(h, n, expect, body, from):
  +h = h
  +n = n
  +expect = expect
  +heads = Spec.History.heads(h, n)
  Shared.Bool.when(
    Result<&2, &2, Spec.Refused, Spec.Committed>,
    Spec.Ids.is_eq(expect, heads),
    u => History.commit.of(h, n, Spec.Node{n, expect, body, from}),
    u => Fail{Spec.Refused{heads}}
  )
