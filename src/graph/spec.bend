import Base
import ../conditions/spec.bend as Cond
import ../glob/spec.bend as Glob
import ../shared.bend as Shared

# The graph of resources: who refers to whom, through which view, for which
# items, and when. One graph holds every edge with its condition, so a
# question about many configurations is asked once, not once per
# configuration. Cycles are allowed: resources may refer to each other.

# The views, built into the core.
type ViewId is Data:
  TextView{}
  BendView{}
  CView{}

# What an edge points at: a resource by name, or a reference that its view
# could not turn into a name (a C include of <stdio.h>, say). An edge may
# point at a resource or an item that does not exist yet; it stays, and
# resolves when that appears.
type Target is Data:
  Named{name: Shared.Name}
  Unresolved{text: String}

# Relative references
# -------------------

# the path of the directory of rest, as segments: all but the last
def Path.dir(rest: String) -> List<&2, String>:
  +segs = String.split(rest, '/')
  List.take(&2, String, segs, Nat.sub(List.length(&2, String, segs), 1n))

# k of dir without its last segment, or None when dir is the root
def Path.walk.up(
  dir: List<&2, String>,
  k: List<&2, String> -> Maybe<&2, List<&2, String>>
) -> Maybe<&2, List<&2, String>>:
  match dir:
    case Nil{}:
      None{}
    case Con{d, r}:
      k(r)

# the segments of dir (last first) after the relative segments rel, or None
# when a ".." climbs out of the root
def Path.walk(rel: List<&2, String>, dir: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match rel:
    case Nil{}:
      Some{dir}
    case Con{+x, +t}:
      +dir = dir
      Shared.Bool.when(
        Maybe<&2, List<&2, String>>,
        String.eq(x, "."),
        u => Path.walk(t, dir),
        u => Shared.Bool.when(
          Maybe<&2, List<&2, String>>,
          String.eq(x, ".."),
          v => Path.walk.up(dir, r => Path.walk(t, r)),
          v => Path.walk(t, x <> dir)
        )
      )

# the target of the walked segments (last first), or unresolved p
def Target.resolve.of(w: Maybe<&2, List<&2, String>>, p: String) -> Target:
  match w:
    case None{}:
      Unresolved{p}
    case Some{segs}:
      +path = String.join(List.reverse(&2, String, segs), "/")
      Shared.Bool.when(
        Target,
        Glob.is_path(path),
        u => Named{Shared.Name{Shared.FileScheme{}, path}},
        u => Unresolved{p}
      )

# the target of a relative import path p from the resource n: a file name
# when the path stays inside the root and is a valid path, else unresolved
def Target.resolve(n: Shared.Name, +p: String) -> Target:
  match n:
    case Shared.Name{Shared.FileScheme{}, rest}:
      Target.resolve.of(
        Path.walk(String.split(p, '/'), List.reverse(&2, String, Path.dir(rest))),
        p
      )

# Which part of the target matters to the source: all of it, or only the
# items with these keys.
type Selection is Data:
  Whole{}
  Items{keys: List<&2, String>}

# A reference from one resource to another, active when cond holds.
type Edge is Data:
  Edge{from: Shared.Name, to: Target, view: ViewId, select: Selection, cond: Cond.Cond}

# where e points
def Edge.to(e: Edge) -> Target:
  match e:
    case Edge{f, t, v, s, c}:
      t

# what e selects
def Edge.select(e: Edge) -> Selection:
  match e:
    case Edge{f, t, v, s, c}:
      s

# when e is active
def Edge.cond(e: Edge) -> Cond.Cond:
  match e:
    case Edge{f, t, v, s, c}:
      c

# The edges.
type Graph is Data:
  Graph{edges: List<&2, Edge>}

# What changed in a resource: its content, with no item keys known (a view
# without items), or exactly the items with these keys.
type Change is Data:
  Content{}
  Keys{keys: List<&2, String>}

# some key of ks is in cs
def Keys.meet(ks: List<&2, String>, +cs: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{k, t}:
      List.any.if(u => Keys.meet(t, cs), List.contains(~String, ~String.eq, cs, k))

# a change touches a selection: any change touches Whole; an unkeyed change
# touches every selection; keyed changes touch the items they name
def Selection.touches(s: Selection, c: Change) -> Bool:
  match s c:
    case Whole{} _:
      True{}
    case Items{ks} Content{}:
      True{}
    case Items{ks} Keys{cs}:
      Keys.meet(ks, cs)

# the edge points at the resource n
def Target.is(t: Target, n: Shared.Name) -> Bool:
  match t:
    case Named{m}:
      String.eq(Shared.Name.show(m), Shared.Name.show(n))
    case Unresolved{x}:
      False{}

# a and b are the same view
def ViewId.is_eq(a: ViewId, b: ViewId) -> Bool:
  match a b:
    case TextView{} TextView{}:
      True{}
    case BendView{} BendView{}:
      True{}
    case CView{} CView{}:
      True{}
    case _ _:
      False{}

# a and b are the same target
def Target.is_eq(a: Target, b: Target) -> Bool:
  match a b:
    case Named{x} Named{y}:
      String.eq(Shared.Name.show(x), Shared.Name.show(y))
    case Unresolved{x} Unresolved{y}:
      String.eq(x, y)
    case _ _:
      False{}

# xs and ys are the same keys in the same order
def Keys.is_eq(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Keys.is_eq(xt, yt), String.eq(x, y))
    case _ _:
      False{}

# a and b are the same selection
def Selection.is_eq(a: Selection, b: Selection) -> Bool:
  match a b:
    case Whole{} Whole{}:
      True{}
    case Items{x} Items{y}:
      Keys.is_eq(x, y)
    case _ _:
      False{}

# a and b are the same edge
def Edge.is_eq(a: Edge, b: Edge) -> Bool:
  match a b:
    case Edge{f1, t1, v1, s1, c1} Edge{f2, t2, v2, s2, c2}:
      List.all.if(
        x => List.all.if(
          u => List.all.if(
            v => List.all.if(w => Cond.Cond.is_eq(c1, c2), Selection.is_eq(s1, s2)),
            ViewId.is_eq(v1, v2)
          ),
          Target.is_eq(t1, t2)
        ),
        String.eq(Shared.Name.show(f1), Shared.Name.show(f2))
      )

# g has the edge e
def Graph.has(g: Graph, e: Edge) -> Bool:
  match g:
    case Graph{es}:
      List.contains(~Edge, ~Edge.is_eq, es, e)

# Questions
# ---------

# the edges of g that a change c to the resource n touches, in some
# configuration where under also holds
law Graph.affected:
  for g: Graph
  for n: Shared.Name
  for c: Change
  for under: Cond.Cond
  List<&2, Edge>

# an edge is affected exactly when it is in g, points at n, its selection
# meets the change, and its condition can hold together with under; so an
# importer that does not use what changed is left alone
law affected_exact:
  for g: Graph
  for n: Shared.Name
  for c: Change
  for under: Cond.Cond
  for e: Edge
  {
    List.contains(
      ~Edge,
      ~Edge.is_eq,
      Graph.affected(g, n, c, under),
      e
    )
      == Bool.and(
        Graph.has(g, e),
        Bool.and(
          Target.is(Edge.to(e), n),
          Bool.and(
            Selection.touches(Edge.select(e), c),
            Cond.Sat.is_holds(Cond.Cond.sat(Cond.And{Edge.cond(e), under}))
          )
        )
      ): Bool
  }
