import Base
import ../conditions/impl.bend as CondImpl
import ../conditions/spec.bend as Cond
import ../shared/bools.bend as Bools
import ../shared/resources.bend as Resources
import ./spec.bend as Spec

# the edge e is affected: it points at n, its selection meets c, and its
# condition can hold together with under
def Graph.hits(+e: Spec.Edge, n: Resources.Name, c: Spec.Change, under: Cond.Cond) -> Bool:
  List.all.if(
    v => List.all.if(
      u => Cond.Sat.is_holds(Cond.Cond.sat(Cond.And{Spec.Edge.cond(e), under})),
      Spec.Selection.touches(Spec.Edge.select(e), c)
    ),
    Spec.Target.is(Spec.Edge.to(e), n)
  )

# the affected edges among es
def Graph.affected.go(
  es: List<&2, Spec.Edge>,
  +n: Resources.Name,
  +c: Spec.Change,
  +under: Cond.Cond
) -> List<&2, Spec.Edge>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      +rest = Graph.affected.go(t, n, c, under)
      Bools.Bool.when(List<&2, Spec.Edge>, Graph.hits(e, n, c, under), u => e <> rest, u => rest)

def Spec.Graph.affected(g, n, c, under):
  match g:
    case Spec.Graph{es}:
      Graph.affected.go(es, n, c, under)
