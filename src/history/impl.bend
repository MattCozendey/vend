import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ./spec.bend as Spec

# An add stores the node under its id and makes it a tip of its resource in
# place of its parents; a node that is there already changes nothing.
# History.join is not written yet.

# a before b, by bytes: the first differing byte decides; a prefix comes
# first
def Ids.lt(a: Shared.Bytes(), b: Shared.Bytes()) -> Bool:
  match a b:
    case Nil{} Con{y, yt}:
      True{}
    case Con{+x, xt} Con{+y, yt}:
      Shared.Bool.when(Bool, U32.is_eq(x, y), u => Ids.lt(xt, yt), u => (x < y: U32))
    case _ _:
      False{}

# xs, sorted ascending, with x, once
def Ids.insert(+x: Shared.Bytes(), xs: List<&2, Shared.Bytes()>) -> List<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      [x]
    case Con{+y, +t}:
      Shared.Bool.when(
        List<&2, Shared.Bytes()>,
        Shared.Bytes.is_eq(x, y),
        u => Con{y, t},
        u => Shared.Bool.when(
          List<&2, Shared.Bytes()>,
          Ids.lt(x, y),
          v => Con{x, Con{y, t}},
          v => Con{y, Ids.insert(x, t)}
        )
      )

# xs without the ids of ps
def Ids.without(
  xs: List<&2, Shared.Bytes()>,
  +ps: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Shared.Bool.when(
        List<&2, Shared.Bytes()>,
        Spec.Ids.has(ps, x),
        u => Ids.without(t, ps),
        u => Con{x, Ids.without(t, ps)}
      )

# the first id of xs that h lacks, or None
def Ids.missing(+h: Spec.History, xs: List<&2, Shared.Bytes()>) -> Maybe<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Bytes()>,
        Spec.History.has(h, x),
        u => Ids.missing(h, t),
        u => Some{x}
      )

# h with the node v under its id x, a tip of its resource in place of its
# parents
def History.put(h: Spec.History, +x: Shared.Bytes(), +v: Spec.Node) -> Spec.History:
  match h:
    case Spec.History{ns, +ts}:
      +key = Shared.Name.show(Spec.Node.name(v))
      old = Maybe.default(
        &2,
        List<&2, Shared.Bytes()>,
        Shared.Table.get(List<&2, Shared.Bytes()>, ts, key),
        []
      )
      tips = Ids.insert(x, Ids.without(old, Spec.Node.parents(v)))
      nodes = Shared.Table.set(Spec.Node, ns, Hash.Hash.hex(x), v)
      Spec.History{nodes, Shared.Table.set(List<&2, Shared.Bytes()>, ts, key, tips)}

# the add of v, given the missing parent if any
def History.add.of(
  +h: Spec.History,
  +v: Spec.Node,
  miss: Maybe<&2, Shared.Bytes()>
) -> Result<&2, &2, Spec.Missing, Spec.Added>:
  match miss:
    case Some{p}:
      Fail{Spec.Missing{p}}
    case None{}:
      +x = Spec.Node.id(v)
      Shared.Bool.when(
        Result<&2, &2, Spec.Missing, Spec.Added>,
        Spec.History.has(h, x),
        u => Done{Spec.Added{h, x}},
        u => Done{Spec.Added{History.put(h, x, v), x}}
      )

def Spec.History.add(h, v):
  +h = h
  +v = v
  History.add.of(h, v, Ids.missing(h, Spec.Node.parents(v)))
