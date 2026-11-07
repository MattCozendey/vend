import Base
import ./bools.bend as Bools
import ./shared.bend as Shared

# Reachability
# ------------
# A graph is a value g, the successors succ(g)(x) of each node x, and the nodes
# nodes(g) that have successors. A search goes one level at a time: a level is
# a list of nodes, and the next level holds the successors of each. It goes as
# deep as the graph has nodes, which is deep enough: a shortest path visits
# each node once.

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a search, a path and a chain keep each and/or as one value, for the proofs to split on
# the successors of each node of xs
def Reach.next(
  ~A: Data,
  ~V: Data,
  ~succ: V -> A -> List<&2, A>,
  xs: List<&2, A>,
  +g: V
) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(&2, A, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g))

# m is in the level xs, or in one of the f levels below it
def Reach.go(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  f: Nat,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> Bool:
  match f:
    case 0n:
      Shared.List.has(~A, ~same, xs, m)
    case 1n+e:
      Bool.or(
        Shared.List.has(~A, ~same, xs, m),
        Reach.go(~A, ~V, ~same, ~succ, e, Reach.next(~A, ~V, ~succ, xs, g), g, m)
      )

# m is a successor of x, or a successor of one, at any depth
def Reach.in(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  +g: V,
  x: A,
  m: A
) -> Bool:
  Reach.go(~A, ~V, ~same, ~succ, List.length(&2, A, nodes(g)), succ(g)(x), g, m)

# a node of ys is c, or has c inside it: setting c's successors to ys would
# close a cycle
def Reach.closes(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  +g: V,
  +c: A,
  ys: List<&2, A>
) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{+y, r}:
      Bool.or(
        Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)),
        Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r)
      )

# Paths
# -----
# A path ps from the level xs to m: its first node is in xs, each next node is
# a successor of the one before, and m is a successor of the last. The proofs
# turn a search into a path and back, and cut a path down to one that visits
# each node once.
def Reach.path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ps: List<&2, A>,
  xs: List<&2, A>,
  +g: V,
  m: A
) -> Bool:
  match ps:
    case Nil{}:
      Shared.List.has(~A, ~same, xs, m)
    case Con{+p, r}:
      Bool.and(
        Shared.List.has(~A, ~same, xs, p),
        Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
      )

# ps has at most f nodes
def Reach.fits(-A: Data, ps: List<&2, A>, f: Nat) -> Bool:
  match ps f:
    case Nil{} n:
      True{}
    case Con{p, r} 0n:
      False{}
    case Con{p, r} 1n+n:
      Reach.fits(A, r, n)

# no node of ps comes twice
def Reach.distinct(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, +r}:
      Bool.and(Bool.not(Shared.List.has(~A, ~same, r, p)), Reach.distinct(~A, ~same, r))

# every node of ps is in ks
def Reach.within(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>, +ks: List<&2, A>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, r}:
      Bool.and(Shared.List.has(~A, ~same, ks, p), Reach.within(~A, ~same, r, ks))

# the nodes of ps after the first that is p
def Reach.after(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>, +p: A) -> List<&2, A>:
  match ps:
    case Nil{}:
      []
    case Con{x, +r}:
      Bools.Bool.when(List<&2, A>, same(x, p), u => r, u => Reach.after(~A, ~same, r, p))

# the first node of ps, or m
def Reach.first(-A: Data, ps: List<&2, A>, m: A) -> A:
  match ps:
    case Nil{}:
      m
    case Con{p, r}:
      p

# Reach.next_found when q is not a successor of x: then a node of r has it
def Reach.next_found.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  x: A,
  r: List<&2, A>,
  g: V,
  q: A,
  w: &y: A -> {
    Shared.List.has(~A, ~same, r, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool}
) -> &y:
  A -> {
    Shared.List.has(~A, ~same, x <> r, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match w:
    case (+y, (h1, h2)):
      (y, (Shared.List.has_cons(~A, ~same, x, r, y)(h1), h2))

# Reach.next_found at the first node x of xs, by whether q is its successor
# (hit)
def Reach.next_found.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  g: V,
  q: A,
  ih: {
    Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q) == True{}: Bool
  } -> &y: A -> {
    Shared.List.has(~A, ~same, r, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool}
) -> {
  Shared.List.has(~A, ~same, succ(g)(x), q) == hit: Bool
} -> {
  Bool.or(hit, Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)) == True{}: Bool
} -> &y:
  A -> {
    Shared.List.has(~A, ~same, x <> r, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match hit:
    case True{}:
      +e => +h =>
        (x, ((
              %Equal.sym(Bool, same(x, x), True{}, refl(x)): {List.any.if(u => Shared.List.has(~A, ~same, r, x), _) == True{}: Bool}
              {==}), e))
    case False{}:
      +e => +h => Reach.next_found.cons(~A, ~V, ~same, ~succ, x, r, g, q, ih(h))

# a node q of the next level is a successor of a node of xs
def Reach.next_found(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +xs: List<&2, A>,
  +g: V,
  +q: A
) -> {Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q) == True{}: Bool} -> &y:
  A -> {
    Shared.List.has(~A, ~same, xs, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match xs:
    case Nil{}:
      +h => Empty.absurd(
        &y: A -> {
          Shared.List.has(~A, ~same, [], y) == True{}: Bool
        }
          & {Shared.List.has(~A, ~same, succ(g)(y), q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      +h =>
        Reach.next_found.at(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~refl,
          Shared.List.has(~A, ~same, succ(g)(x), q),
          x,
          r,
          g,
          q,
          Reach.next_found(~A, ~V, ~same, ~succ, ~refl, r, g, q)
        )({==})((
            %Shared.List.has_append(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g), q): {_ == True{}: Bool}
            h))

# Reach.path_step when ps has a first node p, once the node y before it is found
def Reach.path_step.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  xs: List<&2, A>,
  p: A,
  r: List<&2, A>,
  g: V,
  m: A,
  hr: {Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m) == True{}: Bool},
  w: &y: A -> {
    Shared.List.has(~A, ~same, xs, y) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, succ(g)(y), p) == True{}: Bool}
) -> &y:
  A -> {
    Shared.List.has(~A, ~same, xs, y) == True{}: Bool
  }
    & {Reach.path(~A, ~V, ~same, ~succ, p <> r, succ(g)(y), g, m) == True{}: Bool}:
  match w:
    case (y, (h1, h2)):
      (y, (h1, (
            %Equal.sym(Bool, Shared.List.has(~A, ~same, succ(g)(y), p), True{}, h2): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)) == True{}: Bool}
            hr)))

# a path from the next level starts at a successor of a node of xs
def Reach.path_step(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +xs: List<&2, A>,
  +ps: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool
} -> &y:
  A -> {
    Shared.List.has(~A, ~same, xs, y) == True{}: Bool
  }
    & {Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => Reach.next_found(~A, ~V, ~same, ~succ, ~refl, xs, g, m)(h)
    case Con{+p, +r}:
      +h => Reach.path_step.cons(
        ~A,
        ~V,
        ~same,
        ~succ,
        xs,
        p,
        r,
        g,
        m,
        Bools.Bool.and_true_right(
          Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), p),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
        )(h),
        Reach.next_found(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~refl,
          xs,
          g,
          p
        )(
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        )
      )

# Reach.go_path below the first level, once the node y before the path is found
def Reach.go_path.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  xs: List<&2, A>,
  ps: List<&2, A>,
  e: Nat,
  g: V,
  m: A,
  hf: {Reach.fits(A, ps, e) == True{}: Bool},
  w: &y: A -> {
    Shared.List.has(~A, ~same, xs, y) == True{}: Bool
  }
    & {Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m) == True{}: Bool}
) -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.fits(A, qs, 1n+e) == True{}: Bool}:
  match w:
    case (y, (h1, h2)):
      (y <> ps, ((
            %Equal.sym(Bool, Shared.List.has(~A, ~same, xs, y), True{}, h1): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m)) == True{}: Bool}
            h2), hf))

# Reach.go_path below the first level, once a path from the next level is found
def Reach.go_path.lift(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +xs: List<&2, A>,
  e: Nat,
  +g: V,
  +m: A,
  w: &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool
  }
    & {Reach.fits(A, ps, e) == True{}: Bool}
) -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.fits(A, qs, 1n+e) == True{}: Bool}:
  match w:
    case (+ps, (hp, hf)):
      Reach.go_path.cons(
        ~A,
        ~V,
        ~same,
        ~succ,
        xs,
        ps,
        e,
        g,
        m,
        hf,
        Reach.path_step(~A, ~V, ~same, ~succ, ~refl, xs, ps, g, m)(hp)
      )

# Reach.go_path one level down, by whether m is in the first level (hit)
def Reach.go_path.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +hit: Bool,
  e: Nat,
  xs: List<&2, A>,
  g: V,
  m: A,
  ih: {
    Reach.go(~A, ~V, ~same, ~succ, e, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool
  } -> &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool
  }
    & {Reach.fits(A, ps, e) == True{}: Bool}
) -> {
  Shared.List.has(~A, ~same, xs, m) == hit: Bool
} -> {
  Bool.or(
    hit,
    Reach.go(~A, ~V, ~same, ~succ, e, Reach.next(~A, ~V, ~succ, xs, g), g, m)
  )
    == True{}: Bool
} -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.fits(A, qs, 1n+e) == True{}: Bool}:
  match hit:
    case True{}:
      +he => +h => ([], (he, {==}))
    case False{}:
      +he => +h => Reach.go_path.lift(~A, ~V, ~same, ~succ, ~refl, xs, e, g, m, ih(h))

# a search that finds m has a path to m, no longer than the search is deep
def Reach.go_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  +f: Nat,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> {Reach.go(~A, ~V, ~same, ~succ, f, xs, g, m) == True{}: Bool} -> &ps:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool
  }
    & {Reach.fits(A, ps, f) == True{}: Bool}:
  match f:
    case 0n:
      +h => ([], (h, {==}))
    case 1n+e:
      +h => Reach.go_path.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~refl,
        Shared.List.has(~A, ~same, xs, m),
        e,
        xs,
        g,
        m,
        Reach.go_path(~A, ~V, ~same, ~succ, ~refl, e, Reach.next(~A, ~V, ~succ, xs, g), g, m)
      )({==})(h)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.found_sub at the first node x of xs, by whether it is p (hit)
def Reach.found_sub.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  p: A,
  +q: A,
  +g: V,
  ih: {
    Shared.List.has(~A, ~same, r, p) == True{}: Bool
  } -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q) == True{}: Bool}
) -> {
  same(x, p) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
} -> {
  Shared.List.has(
    ~A,
    ~same,
    List.append(&2, A, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g)),
    q
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +h => +hq =>
        %Equal.sym(
          Bool,
          Shared.List.has(
            ~A,
            ~same,
            List.append(&2, A, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g)),
            q
          ),
          Bool.or(
            Shared.List.has(~A, ~same, succ(g)(x), q),
            Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)
          ),
          Shared.List.has_append(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g), q)
        ): {_ == True{}: Bool}
        %Equal.sym(
          A,
          x,
          p,
          sound(x)(p)(he)
        ): {
          Bool.or(
            Shared.List.has(~A, ~same, succ(g)(_), q),
            Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, succ(g)(p), q),
          True{},
          hq
        ): {
          Bool.or(_, Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)) == True{}: Bool
        }
        {==}
    case False{}:
      +he => +h => +hq =>
        %Equal.sym(
          Bool,
          Shared.List.has(
            ~A,
            ~same,
            List.append(&2, A, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g)),
            q
          ),
          Bool.or(
            Shared.List.has(~A, ~same, succ(g)(x), q),
            Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)
          ),
          Shared.List.has_append(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g), q)
        ): {_ == True{}: Bool}
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q),
          True{},
          ih(h)(hq)
        ): {Bool.or(Shared.List.has(~A, ~same, succ(g)(x), q), _) == True{}: Bool}
        Bools.Bool.or_true_right(Shared.List.has(~A, ~same, succ(g)(x), q))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a successor q of a node p of xs is in the next level
def Reach.found_sub(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +xs: List<&2, A>,
  +p: A,
  +q: A,
  +g: V
) -> {
  Shared.List.has(~A, ~same, xs, p) == True{}: Bool
} -> {
  Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
} -> {Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q) == True{}: Bool}:
  match xs:
    case Nil{}:
      +h => +hq => Empty.absurd(
        {Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, [], g), q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      +h => Reach.found_sub.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        same(x, p),
        x,
        r,
        p,
        q,
        g,
        Reach.found_sub(~A, ~V, ~same, ~succ, ~sound, r, p, q, g)
      )({==})(h)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a path from a successor of a node p of xs is a path from the next level
def Reach.path_sub(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  xs: List<&2, A>,
  +p: A,
  +r: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Shared.List.has(~A, ~same, xs, p) == True{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, r, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool}:
  match r:
    case Nil{}:
      +hp => +h => Reach.found_sub(~A, ~V, ~same, ~succ, ~sound, xs, p, m, g)(hp)(h)
    case Con{+q, +r2}:
      +hp => +h =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q),
          True{},
          Reach.found_sub(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~sound,
            xs,
            p,
            q,
            g
          )(
            hp
          )(
            Bools.Bool.and_true_left(
              Shared.List.has(~A, ~same, succ(g)(p), q),
              Reach.path(~A, ~V, ~same, ~succ, r2, succ(g)(q), g, m)
            )(h)
          )
        ): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, r2, succ(g)(q), g, m)) == True{}: Bool}
        Bools.Bool.and_true_right(
          Shared.List.has(~A, ~same, succ(g)(p), q),
          Reach.path(~A, ~V, ~same, ~succ, r2, succ(g)(q), g, m)
        )(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a path no longer than f makes a search f levels deep find its end
def Reach.path_go(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ps: List<&2, A>,
  +f: Nat,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool
} -> {
  Reach.fits(A, ps, f) == True{}: Bool
} -> {Reach.go(~A, ~V, ~same, ~succ, f, xs, g, m) == True{}: Bool}:
  match ps f:
    case Nil{} 0n:
      +h => +hf => h
    case Nil{} 1n+e:
      +h => +hf =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, xs, m),
          True{},
          h
        ): {
          Bool.or(
            _,
            Reach.go(~A, ~V, ~same, ~succ, e, Reach.next(~A, ~V, ~succ, xs, g), g, m)
          )
            == True{}: Bool
        }
        {==}
    case Con{+p, +r} 0n:
      +h => +hf => Empty.absurd(
        {Reach.go(~A, ~V, ~same, ~succ, 0n, xs, g, m) == True{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+p, +r} 1n+e:
      +h => +hf =>
        %Equal.sym(
          Bool,
          Reach.go(~A, ~V, ~same, ~succ, e, Reach.next(~A, ~V, ~succ, xs, g), g, m),
          True{},
          Reach.path_go(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~sound,
            r,
            e,
            Reach.next(~A, ~V, ~succ, xs, g),
            g,
            m
          )(
            Reach.path_sub(
              ~A,
              ~V,
              ~same,
              ~succ,
              ~sound,
              xs,
              p,
              r,
              g,
              m
            )(
              Bools.Bool.and_true_left(
                Shared.List.has(~A, ~same, xs, p),
                Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
              )(h)
            )(
              Bools.Bool.and_true_right(
                Shared.List.has(~A, ~same, xs, p),
                Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
              )(h)
            )
          )(hf)
        ): {Bool.or(Shared.List.has(~A, ~same, xs, m), _) == True{}: Bool}
        Bools.Bool.or_true_right(Shared.List.has(~A, ~same, xs, m))

# a path to h, then a path from h to m, is a path to m
def Reach.path_append(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +a: List<&2, A>,
  +xs: List<&2, A>,
  +h: A,
  b: List<&2, A>,
  +g: V,
  m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, a, xs, g, h) == True{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, b, succ(g)(h), g, m) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, List.append(&2, A, a, h <> b), xs, g, m) == True{}: Bool}:
  match a:
    case Nil{}:
      +ha => +hb =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, xs, h),
          True{},
          ha
        ): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, b, succ(g)(h), g, m)) == True{}: Bool}
        hb
    case Con{+p, +r}:
      +ha => +hb =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, xs, p),
          True{},
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, h)
          )(ha)
        ): {
          Bool.and(
            _,
            Reach.path(~A, ~V, ~same, ~succ, List.append(&2, A, r, h <> b), succ(g)(p), g, m)
          )
            == True{}: Bool
        }
        Reach.path_append(
          ~A,
          ~V,
          ~same,
          ~succ,
          r,
          succ(g)(p),
          h,
          b,
          g,
          m
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, h)
          )(ha)
        )(hb)

# a path starts in its level
def Reach.path_first(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ps: List<&2, A>,
  ys: List<&2, A>,
  +g: V,
  m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {Shared.List.has(~A, ~same, ys, Reach.first(A, ps, m)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => h
    case Con{+p, r}:
      +h => Bools.Bool.and_true_left(
        Shared.List.has(~A, ~same, ys, p),
        Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
      )(h)

# the nodes of a path have successors, so they are nodes of the graph
def Reach.path_within(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  +ps: List<&2, A>,
  +ys: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {Reach.within(~A, ~same, ps, nodes(g)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => {==}
    case Con{+p, +r}:
      +h =>
        hf = Reach.path_first(
          ~A,
          ~V,
          ~same,
          ~succ,
          r,
          succ(g)(p),
          g,
          m
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, ys, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        )
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, nodes(g), p),
          True{},
          live(g)(p)(Reach.first(A, r, m))(hf)
        ): {Bool.and(_, Reach.within(~A, ~same, r, nodes(g))) == True{}: Bool}
        Reach.path_within(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~nodes,
          ~live,
          r,
          succ(g)(p),
          g,
          m
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, ys, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        )

# Reach.after_path at the first node x of rs, by whether it is p (hit)
def Reach.after_path.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  p: A,
  ys: List<&2, A>,
  +g: V,
  m: A,
  ih: {
    Shared.List.has(~A, ~same, r, p) == True{}: Bool
  } -> {
    Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m) == True{}: Bool
  } -> {
    Reach.path(~A, ~V, ~same, ~succ, Reach.after(~A, ~same, r, p), succ(g)(p), g, m) == True{}: Bool
  }
) -> {
  same(x, p) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  Bool.and(
    Shared.List.has(~A, ~same, ys, x),
    Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
  )
    == True{}: Bool
} -> {
  Reach.path(
    ~A,
    ~V,
    ~same,
    ~succ,
    Bools.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p)),
    succ(g)(p),
    g,
    m
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +hf => +hp =>
        %sound(x)(p)(he): {Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(_), g, m) == True{}: Bool}
        Bools.Bool.and_true_right(
          Shared.List.has(~A, ~same, ys, x),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
        )(hp)
    case False{}:
      +he => +hf => +hp => ih(
        hf
      )(
        Bools.Bool.and_true_right(
          Shared.List.has(~A, ~same, ys, x),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
        )(hp)
      )

# what follows a node p of a path is a path from p's successors
def Reach.after_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +rs: List<&2, A>,
  +p: A,
  ys: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Shared.List.has(~A, ~same, rs, p) == True{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, rs, ys, g, m) == True{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, Reach.after(~A, ~same, rs, p), succ(g)(p), g, m) == True{}: Bool
}:
  match rs:
    case Nil{}:
      +hf => +hp => Empty.absurd(
        {Reach.path(~A, ~V, ~same, ~succ, [], succ(g)(p), g, m) == True{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+x, +r}:
      +hf => Reach.after_path.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        same(x, p),
        x,
        r,
        p,
        ys,
        g,
        m,
        Reach.after_path(~A, ~V, ~same, ~succ, ~sound, r, p, succ(g)(x), g, m)
      )({==})(hf)

# Reach.after_distinct at the first node x, by whether it is p (hit)
def Reach.after_distinct.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  +hit: Bool,
  x: A,
  +r: List<&2, A>,
  p: A,
  ih: {
    Reach.distinct(~A, ~same, r) == True{}: Bool
  } -> {Reach.distinct(~A, ~same, Reach.after(~A, ~same, r, p)) == True{}: Bool}
) -> {
  same(x, p) == hit: Bool
} -> {
  Bool.and(Bool.not(Shared.List.has(~A, ~same, r, x)), Reach.distinct(~A, ~same, r)) == True{}: Bool
} -> {
  Reach.distinct(
    ~A,
    ~same,
    Bools.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p))
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +hd => Bools.Bool.and_true_right(
        Bool.not(Shared.List.has(~A, ~same, r, x)),
        Reach.distinct(~A, ~same, r)
      )(hd)
    case False{}:
      +he => +hd => ih(
        Bools.Bool.and_true_right(
          Bool.not(Shared.List.has(~A, ~same, r, x)),
          Reach.distinct(~A, ~same, r)
        )(hd)
      )

# what follows a node of a path that visits each node once visits each once
def Reach.after_distinct(
  ~A: Data,
  ~same: A -> A -> Bool,
  +rs: List<&2, A>,
  +p: A
) -> {
  Reach.distinct(~A, ~same, rs) == True{}: Bool
} -> {Reach.distinct(~A, ~same, Reach.after(~A, ~same, rs, p)) == True{}: Bool}:
  match rs:
    case Nil{}:
      +h => {==}
    case Con{+x, +r}:
      Reach.after_distinct.at(
        ~A,
        ~same,
        same(x, p),
        x,
        r,
        p,
        Reach.after_distinct(~A, ~same, r, p)
      )({==})

# Reach.after_free at the first node x, by whether it is p (hit)
def Reach.after_free.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hit: Bool,
  +x: A,
  +r: List<&2, A>,
  p: A,
  ih: {
    Reach.distinct(~A, ~same, r) == True{}: Bool
  } -> {
    Shared.List.has(~A, ~same, r, p) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, Reach.after(~A, ~same, r, p), p) == False{}: Bool}
) -> {
  same(x, p) == hit: Bool
} -> {
  Bool.and(Bool.not(Shared.List.has(~A, ~same, r, x)), Reach.distinct(~A, ~same, r)) == True{}: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  Shared.List.has(
    ~A,
    ~same,
    Bools.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p)),
    p
  )
    == False{}: Bool
}:
  match hit:
    case True{}:
      +he => +hd => +hf =>
        %sound(x)(p)(he): {Shared.List.has(~A, ~same, r, _) == False{}: Bool}
        Bools.Bool.not_true(
          Shared.List.has(~A, ~same, r, x)
        )(
          Bools.Bool.and_true_left(
            Bool.not(Shared.List.has(~A, ~same, r, x)),
            Reach.distinct(~A, ~same, r)
          )(hd)
        )
    case False{}:
      +he => +hd => +hf => ih(
        Bools.Bool.and_true_right(
          Bool.not(Shared.List.has(~A, ~same, r, x)),
          Reach.distinct(~A, ~same, r)
        )(hd)
      )(hf)

# p does not come again after its first place in a path that visits each node
# once
def Reach.after_free(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +rs: List<&2, A>,
  +p: A
) -> {
  Reach.distinct(~A, ~same, rs) == True{}: Bool
} -> {
  Shared.List.has(~A, ~same, rs, p) == True{}: Bool
} -> {Shared.List.has(~A, ~same, Reach.after(~A, ~same, rs, p), p) == False{}: Bool}:
  match rs:
    case Nil{}:
      +hd => +hf => Empty.absurd(
        {Shared.List.has(~A, ~same, [], p) == False{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+x, +r}:
      Reach.after_free.at(
        ~A,
        ~same,
        ~sound,
        same(x, p),
        x,
        r,
        p,
        Reach.after_free(~A, ~same, ~sound, r, p)
      )({==})

# Reach.shorten after its first node p, by whether p comes again (hit)
def Reach.shorten.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hit: Bool,
  xs: List<&2, A>,
  +p: A,
  +rs: List<&2, A>,
  +g: V,
  m: A,
  hx: {Shared.List.has(~A, ~same, xs, p) == True{}: Bool},
  hp: {Reach.path(~A, ~V, ~same, ~succ, rs, succ(g)(p), g, m) == True{}: Bool},
  +hd: {Reach.distinct(~A, ~same, rs) == True{}: Bool}
) -> {Shared.List.has(~A, ~same, rs, p) == hit: Bool} -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.distinct(~A, ~same, qs) == True{}: Bool}:
  match hit:
    case False{}:
      +he =>
        (p <> rs, ((
              %Equal.sym(Bool, Shared.List.has(~A, ~same, xs, p), True{}, hx): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, rs, succ(g)(p), g, m)) == True{}: Bool}
              hp), (
              %Equal.sym(Bool, Shared.List.has(~A, ~same, rs, p), False{}, he): {Bool.and(Bool.not(_), Reach.distinct(~A, ~same, rs)) == True{}: Bool}
              hd)))
    case True{}:
      +he =>
        (p <> Reach.after(~A, ~same, rs, p), ((
              %Equal.sym(Bool, Shared.List.has(~A, ~same, xs, p), True{}, hx): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, Reach.after(~A, ~same, rs, p), succ(g)(p), g, m)) == True{}: Bool}
              Reach.after_path(~A, ~V, ~same, ~succ, ~sound, rs, p, succ(g)(p), g, m)(he)(hp)), (
              %Equal.sym(Bool, Shared.List.has(~A, ~same, Reach.after(~A, ~same, rs, p), p), False{}, Reach.after_free(~A, ~same, ~sound, rs, p)(hd)(he)): {Bool.and(Bool.not(_), Reach.distinct(~A, ~same, Reach.after(~A, ~same, rs, p))) == True{}: Bool}
              Reach.after_distinct(~A, ~same, rs, p)(hd))))

# Reach.shorten after its first node p, once the rest is cut
def Reach.shorten.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  xs: List<&2, A>,
  +p: A,
  g: V,
  m: A,
  hx: {Shared.List.has(~A, ~same, xs, p) == True{}: Bool},
  w: &rs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, rs, succ(g)(p), g, m) == True{}: Bool
  }
    & {Reach.distinct(~A, ~same, rs) == True{}: Bool}
) -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.distinct(~A, ~same, qs) == True{}: Bool}:
  match w:
    case (+rs, (hp, hd)):
      Reach.shorten.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        Shared.List.has(~A, ~same, rs, p),
        xs,
        p,
        rs,
        g,
        m,
        hx,
        hp,
        hd
      )({==})

# a path can be cut down to one that visits each node once
def Reach.shorten(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ps: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> {Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool} -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reach.distinct(~A, ~same, qs) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => ([], (h, {==}))
    case Con{+p, +r}:
      +h => Reach.shorten.cons(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        xs,
        p,
        g,
        m,
        Bools.Bool.and_true_left(
          Shared.List.has(~A, ~same, xs, p),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
        )(h),
        Reach.shorten(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~sound,
          r,
          succ(g)(p),
          g,
          m
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        )
      )

# Counting
# --------

# a is at most one more than b, when it is at most b
def Reach.le_succ(
  +a: Nat,
  +b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(a, 1n+b) == True{}: Bool}:
  match a b:
    case 0n y:
      +h => {==}
    case 1n+x 0n:
      +h => Empty.absurd({Nat.is_le(1n+x, 1n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+x 1n+y:
      +h => Reach.le_succ(x, y)(h)

# what fits in a fits in any b that is at least a
def Reach.fits_le(
  -A: Data,
  +ps: List<&2, A>,
  +a: Nat,
  +b: Nat
) -> {
  Reach.fits(A, ps, a) == True{}: Bool
} -> {Nat.is_le(a, b) == True{}: Bool} -> {Reach.fits(A, ps, b) == True{}: Bool}:
  match ps a b:
    case Nil{} x y:
      +hf => +hl => {==}
    case Con{p, r} 0n y:
      +hf => +hl => Empty.absurd(
        {Reach.fits(A, p <> r, y) == True{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+p, +r} 1n+x 0n:
      +hf => +hl => Empty.absurd(
        {Reach.fits(A, p <> r, 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(hl)
      )
    case Con{+p, +r} 1n+x 1n+y:
      +hf => +hl => Reach.fits_le(A, r, x, y)(hf)(hl)

# Reach.drop_le at the first node k, by whether it is p (hit)
def Reach.drop_le.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  +hit: Bool,
  k: A,
  +r: List<&2, A>,
  p: A,
  ih: {
    Nat.is_le(
      List.length(&2, A, Shared.List.remove(~A, ~same, r, p)),
      List.length(&2, A, r)
    )
      == True{}: Bool
  }
) -> {
  Nat.is_le(
    List.length(&2, A, List.filter.put(A, k, Shared.List.remove(~A, ~same, r, p), Bool.not(hit))),
    1n+List.length(&2, A, r)
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      Reach.le_succ(
        List.length(&2, A, Shared.List.remove(~A, ~same, r, p)),
        List.length(&2, A, r)
      )(ih)
    case False{}:
      ih

# dropping nodes leaves no more than there were
def Reach.drop_le(
  ~A: Data,
  ~same: A -> A -> Bool,
  +ks: List<&2, A>,
  +p: A
) -> {
  Nat.is_le(
    List.length(&2, A, Shared.List.remove(~A, ~same, ks, p)),
    List.length(&2, A, ks)
  )
    == True{}: Bool
}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, +r}:
      Reach.drop_le.at(~A, ~same, same(k, p), k, r, p, Reach.drop_le(~A, ~same, r, p))

# Reach.drop_lt at the first node k, by whether it is p (hit)
def Reach.drop_lt.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  +hit: Bool,
  k: A,
  r: List<&2, A>,
  p: A,
  ih: {
    Shared.List.has(~A, ~same, r, p) == True{}: Bool
  } -> {
    Nat.is_le(
      1n+List.length(&2, A, Shared.List.remove(~A, ~same, r, p)),
      List.length(&2, A, r)
    )
      == True{}: Bool
  }
) -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  Nat.is_le(
    1n+List.length(
      &2,
      A,
      List.filter.put(A, k, Shared.List.remove(~A, ~same, r, p), Bool.not(hit))
    ),
    1n+List.length(&2, A, r)
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +h => Reach.drop_le(~A, ~same, r, p)
    case False{}:
      +h => ih(h)

# dropping a node that is there leaves fewer
def Reach.drop_lt(
  ~A: Data,
  ~same: A -> A -> Bool,
  +ks: List<&2, A>,
  +p: A
) -> {
  Shared.List.has(~A, ~same, ks, p) == True{}: Bool
} -> {
  Nat.is_le(
    1n+List.length(&2, A, Shared.List.remove(~A, ~same, ks, p)),
    List.length(&2, A, ks)
  )
    == True{}: Bool
}:
  match ks:
    case Nil{}:
      +h => Empty.absurd(
        {
          Nat.is_le(1n+List.length(&2, A, Shared.List.remove(~A, ~same, [], p)), 0n) == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{k, +r}:
      Reach.drop_lt.at(~A, ~same, same(k, p), k, r, p, Reach.drop_lt(~A, ~same, r, p))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.drop_keep at the first node k, by whether it is p (hk) and q (hq)
def Reach.drop_keep.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hk: Bool,
  +hq: Bool,
  k: A,
  r: List<&2, A>,
  p: A,
  q: A,
  ih: {
    Shared.List.has(~A, ~same, r, q) == True{}: Bool
  } -> {
    same(q, p) == False{}: Bool
  } -> {Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, r, p), q) == True{}: Bool}
) -> {
  same(k, p) == hk: Bool
} -> {
  same(k, q) == hq: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, q), hq) == True{}: Bool
} -> {
  same(q, p) == False{}: Bool
} -> {
  Shared.List.has(
    ~A,
    ~same,
    List.filter.put(A, k, Shared.List.remove(~A, ~same, r, p), Bool.not(hk)),
    q
  )
    == True{}: Bool
}:
  match hk hq:
    case True{} True{}:
      +ek => +eq => +h => +hn =>
        Empty.absurd(
          {Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, r, p), q) == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(Bool, False{}, same(k, p), True{}, Equal.sym(Bool, same(k, p), False{}, (
                  %Equal.sym(A, k, q, sound(k)(q)(eq)): {same(_, p) == False{}: Bool}
                  hn)), ek)
          )
        )
    case True{} False{}:
      +ek => +eq => +h => +hn => ih(h)(hn)
    case False{} True{}:
      +ek => +eq => +h => +hn =>
        %Equal.sym(
          Bool,
          same(k, q),
          True{},
          eq
        ): {
          List.any.if(
            u => Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, r, p), q),
            _
          )
            == True{}: Bool
        }
        {==}
    case False{} False{}:
      +ek => +eq => +h => +hn =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, r, p), q),
          True{},
          ih(h)(hn)
        ): {List.any.if(u => _, same(k, q)) == True{}: Bool}
        Shared.List.any.if_true(same(k, q))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# dropping the nodes that are p keeps the others
def Reach.drop_keep(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ks: List<&2, A>,
  +p: A,
  +q: A
) -> {
  Shared.List.has(~A, ~same, ks, q) == True{}: Bool
} -> {
  same(q, p) == False{}: Bool
} -> {Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, ks, p), q) == True{}: Bool}:
  match ks:
    case Nil{}:
      +h => +hn => Empty.absurd(
        {Shared.List.has(~A, ~same, [], q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+k, +r}:
      Reach.drop_keep.at(
        ~A,
        ~same,
        ~sound,
        same(k, p),
        same(k, q),
        k,
        r,
        p,
        q,
        Reach.drop_keep(~A, ~same, ~sound, r, p, q)
      )({==})({==})

# the nodes of ps, none of them p, stay in ks without p
def Reach.within_drop(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +p: A
) -> {
  Reach.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  Shared.List.has(~A, ~same, ps, p) == False{}: Bool
} -> {Reach.within(~A, ~same, ps, Shared.List.remove(~A, ~same, ks, p)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hw => +hn => {==}
    case Con{+q, +r}:
      +hw => +hn =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, Shared.List.remove(~A, ~same, ks, p), q),
          True{},
          Reach.drop_keep(
            ~A,
            ~same,
            ~sound,
            ks,
            p,
            q
          )(
            Bools.Bool.and_true_left(
              Shared.List.has(~A, ~same, ks, q),
              Reach.within(~A, ~same, r, ks)
            )(hw)
          )(Shared.List.any.if_false_hit(same(q, p), u => Shared.List.has(~A, ~same, r, p))(hn))
        ): {
          Bool.and(
            _,
            Reach.within(~A, ~same, r, Shared.List.remove(~A, ~same, ks, p))
          )
            == True{}: Bool
        }
        Reach.within_drop(
          ~A,
          ~same,
          ~sound,
          r,
          ks,
          p
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, ks, q),
            Reach.within(~A, ~same, r, ks)
          )(hw)
        )(Shared.List.any.if_false_rest(same(q, p), u => Shared.List.has(~A, ~same, r, p))(hn))

# a path that visits each node of ks at most once has no more nodes than ks
def Reach.fits_nodes(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ps: List<&2, A>,
  +ks: List<&2, A>
) -> {
  Reach.distinct(~A, ~same, ps) == True{}: Bool
} -> {
  Reach.within(~A, ~same, ps, ks) == True{}: Bool
} -> {Reach.fits(A, ps, List.length(&2, A, ks)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hd => +hw => {==}
    case Con{+p, +r}:
      +hd => +hw =>
        Reach.fits_le(
          A,
          p <> r,
          1n+List.length(&2, A, Shared.List.remove(~A, ~same, ks, p)),
          List.length(&2, A, ks)
        )(
          Reach.fits_nodes(
            ~A,
            ~same,
            ~sound,
            r,
            Shared.List.remove(~A, ~same, ks, p)
          )(
            Bools.Bool.and_true_right(
              Bool.not(Shared.List.has(~A, ~same, r, p)),
              Reach.distinct(~A, ~same, r)
            )(hd)
          )(
            Reach.within_drop(
              ~A,
              ~same,
              ~sound,
              r,
              ks,
              p
            )(
              Bools.Bool.and_true_right(
                Shared.List.has(~A, ~same, ks, p),
                Reach.within(~A, ~same, r, ks)
              )(hw)
            )(
              Bools.Bool.not_true(
                Shared.List.has(~A, ~same, r, p)
              )(
                Bools.Bool.and_true_left(
                  Bool.not(Shared.List.has(~A, ~same, r, p)),
                  Reach.distinct(~A, ~same, r)
                )(hd)
              )
            )
          )
        )(
          Reach.drop_lt(
            ~A,
            ~same,
            ks,
            p
          )(
            Bools.Bool.and_true_left(
              Shared.List.has(~A, ~same, ks, p),
              Reach.within(~A, ~same, r, ks)
            )(hw)
          )
        )

# Transitivity
# ------------

# Reach.in_through, once both paths are cut to visit each node once
def Reach.in_through.fin(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  +g: V,
  +x: A,
  +m: A,
  w: &qs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, succ(g)(x), g, m) == True{}: Bool
  }
    & {Reach.distinct(~A, ~same, qs) == True{}: Bool}
) -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}:
  match w:
    case (+qs, (+hq, hd)):
      Reach.path_go(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        qs,
        List.length(&2, A, nodes(g)),
        succ(g)(x),
        g,
        m
      )(
        hq
      )(
        Reach.fits_nodes(
          ~A,
          ~same,
          ~sound,
          qs,
          nodes(g)
        )(hd)(Reach.path_within(~A, ~V, ~same, ~succ, ~nodes, ~live, qs, succ(g)(x), g, m)(hq))
      )

# Reach.in_through, once the path from h to m is found
def Reach.in_through.two(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  +g: V,
  +x: A,
  +h: A,
  +m: A,
  +ps1: List<&2, A>,
  h1: {Reach.path(~A, ~V, ~same, ~succ, ps1, succ(g)(x), g, h) == True{}: Bool},
  w: &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(h), g, m) == True{}: Bool
  }
    & {Reach.fits(A, ps, List.length(&2, A, nodes(g))) == True{}: Bool}
) -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}:
  match w:
    case (+ps2, (h2, f2)):
      Reach.in_through.fin(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~sound,
        ~live,
        g,
        x,
        m,
        Reach.shorten(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~sound,
          List.append(&2, A, ps1, h <> ps2),
          succ(g)(x),
          g,
          m
        )(Reach.path_append(~A, ~V, ~same, ~succ, ps1, succ(g)(x), h, ps2, g, m)(h1)(h2))
      )

# Reach.in_through, once the path from x to h is found
def Reach.in_through.one(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  g: V,
  x: A,
  h: A,
  m: A,
  w: &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(x), g, h) == True{}: Bool
  }
    & {Reach.fits(A, ps, List.length(&2, A, nodes(g))) == True{}: Bool},
  w2: &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(h), g, m) == True{}: Bool
  }
    & {Reach.fits(A, ps, List.length(&2, A, nodes(g))) == True{}: Bool}
) -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}:
  match w:
    case (ps1, (h1, f1)):
      Reach.in_through.two(~A, ~V, ~same, ~succ, ~nodes, ~sound, ~live, g, x, h, m, ps1, h1, w2)

# what is inside a node h that is inside x is inside x
def Reach.in_through(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  +g: V,
  +x: A,
  +h: A,
  +m: A
) -> {
  Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, h) == True{}: Bool
} -> {
  Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, h, m) == True{}: Bool
} -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}:
  +a => +b => Reach.in_through.one(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    ~sound,
    ~live,
    g,
    x,
    h,
    m,
    Reach.go_path(~A, ~V, ~same, ~succ, ~refl, List.length(&2, A, nodes(g)), succ(g)(x), g, h)(a),
    Reach.go_path(~A, ~V, ~same, ~succ, ~refl, List.length(&2, A, nodes(g)), succ(g)(h), g, m)(b)
  )
# a search from no nodes finds nothing
def Reach.go_nil(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +f: Nat,
  g: V,
  m: A
) -> {Reach.go(~A, ~V, ~same, ~succ, f, [], g, m) == False{}: Bool}:
  match f:
    case 0n:
      {==}
    case 1n+e:
      Reach.go_nil(~A, ~V, ~same, ~succ, e, g, m)

# a path from x's successors to m makes m inside x
def Reach.path_in(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ps: List<&2, A>,
  +g: V,
  +x: A,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(x), g, m) == True{}: Bool
} -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}:
  +h => Reach.in_through.fin(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    ~sound,
    ~live,
    g,
    x,
    m,
    Reach.shorten(~A, ~V, ~same, ~succ, ~sound, ps, succ(g)(x), g, m)(h)
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.closes_found at the first node x of ys, by whether it is y (hit)
def Reach.closes_found.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  g: V,
  +c: A,
  y: A,
  ih: {
    Shared.List.has(~A, ~same, r, y) == True{}: Bool
  } -> {
    Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool
  } -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r) == True{}: Bool}
) -> {
  same(x, y) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, y), hit) == True{}: Bool
} -> {
  Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool
} -> {
  Bool.or(
    Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c)),
    Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r)
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +h => +hy =>
        %Equal.sym(
          A,
          x,
          y,
          sound(x)(y)(he)
        ): {
          Bool.or(
            Bool.or(same(_, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, _, c)),
            Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r)
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)),
          True{},
          hy
        ): {Bool.or(_, Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r)) == True{}: Bool}
        {==}
    case False{}:
      +he => +h => +hy =>
        %Equal.sym(
          Bool,
          Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r),
          True{},
          ih(h)(hy)
        ): {
          Bool.or(
            Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c)),
            _
          )
            == True{}: Bool
        }
        Bools.Bool.or_true_right(
          Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c))
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a node of ys that is c, or has c inside it, closes a cycle
def Reach.closes_found(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  +ys: List<&2, A>,
  +g: V,
  +c: A,
  +y: A
) -> {
  Shared.List.has(~A, ~same, ys, y) == True{}: Bool
} -> {
  Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool
} -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool}:
  match ys:
    case Nil{}:
      +h => +hy => Empty.absurd(
        {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, []) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      +h => Reach.closes_found.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~sound,
        same(x, y),
        x,
        r,
        g,
        c,
        y,
        Reach.closes_found(~A, ~V, ~same, ~succ, ~nodes, ~sound, r, g, c, y)
      )({==})(h)

# a path from ys to c closes a cycle
def Reach.closes_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  +qs: List<&2, A>,
  +ys: List<&2, A>,
  +g: V,
  +c: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, qs, ys, g, c) == True{}: Bool
} -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool}:
  match qs:
    case Nil{}:
      +h =>
        Reach.closes_found(~A, ~V, ~same, ~succ, ~nodes, ~sound, ys, g, c, c)(h)((
            %Equal.sym(Bool, same(c, c), True{}, refl(c)): {Bool.or(_, Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, c, c)) == True{}: Bool}
            {==}))
    case Con{+y, +r}:
      +h =>
        Reach.closes_found(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~nodes,
          ~sound,
          ys,
          g,
          c,
          y
        )(
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, ys, y),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(y), g, c)
          )(h)
        )((
            %Equal.sym(Bool, Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c), True{}, Reach.path_in(~A, ~V, ~same, ~succ, ~nodes, ~sound, ~live, r, g, y, c)(Bools.Bool.and_true_right(Shared.List.has(~A, ~same, ys, y), Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(y), g, c))(h))): {Bool.or(same(y, c), _) == True{}: Bool}
            Bools.Bool.or_true_right(same(y, c))))

# a path that never leaves c is a path before c's successors were set
def Reach.put_keep(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +ps: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  +m: A
) -> {
  Shared.List.has(~A, ~same, ps, c) == False{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, xs, put(g)(c)(w), m) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hf => +h => h
    case Con{+p, +r}:
      +hf => +h =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, xs, p),
          True{},
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m)
          )(h)
        ): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)) == True{}: Bool}
        Reach.put_keep(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~W,
          ~put,
          ~agree,
          r,
          succ(g)(p),
          g,
          c,
          w,
          m
        )(Shared.List.any.if_false_rest(same(p, c), u => Shared.List.has(~A, ~same, r, c))(hf))((
            %agree(g)(c)(w)(p)(Shared.List.any.if_false_hit(same(p, c), u => Shared.List.has(~A, ~same, r, c))(hf)): {Reach.path(~A, ~V, ~same, ~succ, r, _, put(g)(c)(w), m) == True{}: Bool}
            Bools.Bool.and_true_right(Shared.List.has(~A, ~same, xs, p), Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m))(h)))

# a path that never leaves c stays a path after c's successors are set
def Reach.put_back(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +ps: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  +m: A
) -> {
  Shared.List.has(~A, ~same, ps, c) == False{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, ps, xs, put(g)(c)(w), m) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hf => +h => h
    case Con{+p, +r}:
      +hf => +h =>
        %Equal.sym(
          Bool,
          Shared.List.has(~A, ~same, xs, p),
          True{},
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        ): {
          Bool.and(
            _,
            Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m)
          )
            == True{}: Bool
        }
        %Equal.sym(
          List<&2, A>,
          succ(put(g)(c)(w))(p),
          succ(g)(p),
          agree(
            g
          )(
            c
          )(
            w
          )(p)(Shared.List.any.if_false_hit(same(p, c), u => Shared.List.has(~A, ~same, r, c))(hf))
        ): {Reach.path(~A, ~V, ~same, ~succ, r, _, put(g)(c)(w), m) == True{}: Bool}
        Reach.put_back(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~W,
          ~put,
          ~agree,
          r,
          succ(g)(p),
          g,
          c,
          w,
          m
        )(
          Shared.List.any.if_false_rest(same(p, c), u => Shared.List.has(~A, ~same, r, c))(hf)
        )(
          Bools.Bool.and_true_right(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
          )(h)
        )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.put_first after the first node p, once the rest is cut at c
def Reach.put_first.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  p: A,
  xs: List<&2, A>,
  g: V,
  c: A,
  hx: {Shared.List.has(~A, ~same, xs, p) == True{}: Bool},
  hp: {same(p, c) == False{}: Bool},
  w2: &qs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, succ(g)(p), g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}
) -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}:
  match w2:
    case (qs, (h1, h2)):
      (p <> qs, ((
            %Equal.sym(Bool, Shared.List.has(~A, ~same, xs, p), True{}, hx): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, qs, succ(g)(p), g, c)) == True{}: Bool}
            h1), (
            %Equal.sym(Bool, same(p, c), False{}, hp): {List.any.if(u => Shared.List.has(~A, ~same, qs, c), _) == False{}: Bool}
            h2)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Reach.put_first at the first node p, by whether it is c (hit)
def Reach.put_first.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +hit: Bool,
  +p: A,
  +r: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  +m: A,
  ih: {
    Shared.List.has(~A, ~same, r, c) == True{}: Bool
  } -> {
    Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), put(g)(c)(w), m) == True{}: Bool
  } -> &qs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, succ(g)(p), g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}
) -> {
  same(p, c) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~A, ~same, r, c), hit) == True{}: Bool
} -> {
  Bool.and(
    Shared.List.has(~A, ~same, xs, p),
    Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m)
  )
    == True{}: Bool
} -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}:
  match hit:
    case True{}:
      +he => +hf => +h =>
        ([], ((
              %sound(p)(c)(he): {Shared.List.has(~A, ~same, xs, _) == True{}: Bool}
              Bools.Bool.and_true_left(Shared.List.has(~A, ~same, xs, p), Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m))(h)), {==}))
    case False{}:
      +he => +hf => +h =>
        Reach.put_first.cons(
          ~A,
          ~V,
          ~same,
          ~succ,
          p,
          xs,
          g,
          c,
          Bools.Bool.and_true_left(
            Shared.List.has(~A, ~same, xs, p),
            Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m)
          )(h),
          he,
          ih(hf)((
              %agree(g)(c)(w)(p)(he): {Reach.path(~A, ~V, ~same, ~succ, r, _, put(g)(c)(w), m) == True{}: Bool}
              Bools.Bool.and_true_right(Shared.List.has(~A, ~same, xs, p), Reach.path(~A, ~V, ~same, ~succ, r, succ(put(g)(c)(w))(p), put(g)(c)(w), m))(h)))
        )

# a path that leaves c has a part before c that never leaves c
def Reach.put_first(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +ps: List<&2, A>,
  xs: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  +m: A
) -> {
  Shared.List.has(~A, ~same, ps, c) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, ps, xs, put(g)(c)(w), m) == True{}: Bool} -> &qs:
  List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}:
  match ps:
    case Nil{}:
      +hf => +h => Empty.absurd(
        &qs: List<
          &2,
          A> -> {
          Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, c) == True{}: Bool
        }
          & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+p, +r}:
      +hf => Reach.put_first.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~sound,
        ~W,
        ~put,
        ~agree,
        same(p, c),
        p,
        r,
        xs,
        g,
        c,
        w,
        m,
        Reach.put_first(~A, ~V, ~same, ~succ, ~sound, ~W, ~put, ~agree, r, succ(g)(p), g, c, w, m)
      )({==})(hf)

# Reach.put_closes, once the part before c is cut
def Reach.put_closes.fin(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ys: List<&2, A>,
  g: V,
  c: A,
  w2: &qs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, ys, g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}
) -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool}:
  match w2:
    case (qs, (h1, h2)):
      Reach.closes_path(~A, ~V, ~same, ~succ, ~nodes, ~refl, ~sound, ~live, qs, ys, g, c)(h1)

# Reach.put_closes, by whether the path leaves c (hit)
def Reach.put_closes.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +hit: Bool,
  +ps: List<&2, A>,
  +ys: List<&2, A>,
  +g: V,
  +c: A,
  w: W
) -> {
  Shared.List.has(~A, ~same, ps, c) == hit: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, put(g)(c)(w), c) == True{}: Bool
} -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool}:
  match hit:
    case False{}:
      +e => +h => Reach.closes_path(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~refl,
        ~sound,
        ~live,
        ps,
        ys,
        g,
        c
      )(Reach.put_keep(~A, ~V, ~same, ~succ, ~W, ~put, ~agree, ps, ys, g, c, w, c)(e)(h))
    case True{}:
      +e => +h => Reach.put_closes.fin(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~refl,
        ~sound,
        ~live,
        ys,
        g,
        c,
        Reach.put_first(~A, ~V, ~same, ~succ, ~sound, ~W, ~put, ~agree, ps, ys, g, c, w, c)(e)(h)
      )

# a path from ys to c after c's successors are set means ys closes a cycle
# before
def Reach.put_closes(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +ps: List<&2, A>,
  ys: List<&2, A>,
  g: V,
  +c: A,
  w: W
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, put(g)(c)(w), c) == True{}: Bool
} -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool}:
  Reach.put_closes.at(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    ~refl,
    ~sound,
    ~live,
    ~W,
    ~put,
    ~agree,
    Shared.List.has(~A, ~same, ps, c),
    ps,
    ys,
    g,
    c,
    w
  )({==})

# Reach.put_acyclic for a cycle through x that leaves c: from c's new
# successors back to c
def Reach.put_acyclic.mid(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +x: A,
  +ps: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  hq: {Shared.List.has(~A, ~same, ps, c) == True{}: Bool},
  h: {Reach.path(~A, ~V, ~same, ~succ, ps, succ(put(g)(c)(w))(x), put(g)(c)(w), x) == True{}: Bool},
  w2: &qs: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, qs, succ(put(g)(c)(w))(x), g, c) == True{}: Bool
  }
    & {Shared.List.has(~A, ~same, qs, c) == False{}: Bool}
) -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)) == True{}: Bool}:
  match w2:
    case (+qs, (h1, h2)):
      Reach.put_closes(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~refl,
        ~sound,
        ~live,
        ~W,
        ~put,
        ~agree,
        List.append(&2, A, Reach.after(~A, ~same, ps, c), x <> qs),
        succ(put(g)(c)(w))(c),
        g,
        c,
        w
      )(
        Reach.path_append(
          ~A,
          ~V,
          ~same,
          ~succ,
          Reach.after(~A, ~same, ps, c),
          succ(put(g)(c)(w))(c),
          x,
          qs,
          put(g)(c)(w),
          c
        )(
          Reach.after_path(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~sound,
            ps,
            c,
            succ(put(g)(c)(w))(x),
            put(g)(c)(w),
            x
          )(hq)(h)
        )(
          Reach.put_back(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~W,
            ~put,
            ~agree,
            qs,
            succ(put(g)(c)(w))(x),
            g,
            c,
            w,
            c
          )(h2)(h1)
        )
      )

# Reach.put_acyclic for a cycle ps through x, by whether x is c (hx) and
# whether ps leaves c (hq)
def Reach.put_acyclic.case(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +hx: Bool,
  +hq: Bool,
  +x: A,
  +ps: List<&2, A>,
  +g: V,
  +c: A,
  +w: W,
  acyc: @y: A -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, y) == False{}: Bool},
  hc: {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)) == False{}: Bool}
) -> {
  same(x, c) == hx: Bool
} -> {
  Shared.List.has(~A, ~same, ps, c) == hq: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, succ(put(g)(c)(w))(x), put(g)(c)(w), x) == True{}: Bool
} -> {False{} == True{}: Bool}:
  match hx hq:
    case y True{}:
      +ex => +eq => +h => Equal.trans(
        Bool,
        False{},
        Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)),
        True{},
        Equal.sym(
          Bool,
          Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)),
          False{},
          hc
        ),
        Reach.put_acyclic.mid(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~nodes,
          ~refl,
          ~sound,
          ~live,
          ~W,
          ~put,
          ~agree,
          x,
          ps,
          g,
          c,
          w,
          eq,
          h,
          Reach.put_first(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~sound,
            ~W,
            ~put,
            ~agree,
            ps,
            succ(put(g)(c)(w))(x),
            g,
            c,
            w,
            x
          )(eq)(h)
        )
      )
    case True{} False{}:
      +ex => +eq => +h =>
        Equal.trans(
          Bool,
          False{},
          Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)),
          True{},
          Equal.sym(
            Bool,
            Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)),
            False{},
            hc
          ),
          Reach.put_closes(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~nodes,
            ~refl,
            ~sound,
            ~live,
            ~W,
            ~put,
            ~agree,
            ps,
            succ(put(g)(c)(w))(c),
            g,
            c,
            w
          )((
              %sound(x)(c)(ex): {Reach.path(~A, ~V, ~same, ~succ, ps, succ(put(g)(c)(w))(_), put(g)(c)(w), _) == True{}: Bool}
              h))
        )
    case False{} False{}:
      +ex => +eq => +h =>
        Equal.trans(
          Bool,
          False{},
          Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, x),
          True{},
          Equal.sym(Bool, Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, x), False{}, acyc(x)),
          Reach.path_in(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~nodes,
            ~sound,
            ~live,
            ps,
            g,
            x,
            x
          )(Reach.put_keep(~A, ~V, ~same, ~succ, ~W, ~put, ~agree, ps, succ(g)(x), g, c, w, x)(eq)((
                %agree(g)(c)(w)(x)(ex): {Reach.path(~A, ~V, ~same, ~succ, ps, _, put(g)(c)(w), x) == True{}: Bool}
                h)))
        )

# Reach.put_acyclic, once a cycle through x is found
def Reach.put_acyclic.cyc(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +x: A,
  g: V,
  +c: A,
  w: W,
  acyc: @y: A -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, y) == False{}: Bool},
  hc: {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)) == False{}: Bool},
  w2: &ps: List<
    &2,
    A> -> {
    Reach.path(~A, ~V, ~same, ~succ, ps, succ(put(g)(c)(w))(x), put(g)(c)(w), x) == True{}: Bool
  }
    & {Reach.fits(A, ps, List.length(&2, A, nodes(put(g)(c)(w)))) == True{}: Bool}
) -> {False{} == True{}: Bool}:
  match w2:
    case (+ps, (hp, hf)):
      Reach.put_acyclic.case(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        ~refl,
        ~sound,
        ~live,
        ~W,
        ~put,
        ~agree,
        same(x, c),
        Shared.List.has(~A, ~same, ps, c),
        x,
        ps,
        g,
        c,
        w,
        acyc,
        hc
      )({==})({==})(hp)

# Reach.put_acyclic, by whether x is inside itself after the set (b)
def Reach.put_acyclic.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +b: Bool,
  +x: A,
  +g: V,
  +c: A,
  +w: W,
  acyc: @y: A -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, y) == False{}: Bool},
  hc: {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)) == False{}: Bool}
) -> {
  Reach.in(~A, ~V, ~same, ~succ, ~nodes, put(g)(c)(w), x, x) == b: Bool
} -> {b == False{}: Bool}:
  match b:
    case False{}:
      +e => {==}
    case True{}:
      +e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Reach.put_acyclic.cyc(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~nodes,
            ~refl,
            ~sound,
            ~live,
            ~W,
            ~put,
            ~agree,
            x,
            g,
            c,
            w,
            acyc,
            hc,
            Reach.go_path(
              ~A,
              ~V,
              ~same,
              ~succ,
              ~refl,
              List.length(&2, A, nodes(put(g)(c)(w))),
              succ(put(g)(c)(w))(x),
              put(g)(c)(w),
              x
            )(e)
          )
        )
      )

# setting the successors of c to nodes that do not close a cycle keeps every
# node outside itself
def Reach.put_acyclic(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  ~live: @g: V -> @p: A -> @q: A -> {
    Shared.List.has(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {Shared.List.has(~A, ~same, nodes(g), p) == True{}: Bool},
  ~W: Data,
  ~put: V -> A -> W -> V,
  ~agree: @g: V -> @c: A -> @w: W -> @p: A -> {
    same(p, c) == False{}: Bool
  } -> {succ(put(g)(c)(w))(p) == succ(g)(p): List<&2, A>},
  +g: V,
  +c: A,
  +w: W,
  +x: A
) -> (
  @y: A -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, y) == False{}: Bool}
) -> {
  Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, succ(put(g)(c)(w))(c)) == False{}: Bool
} -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, put(g)(c)(w), x, x) == False{}: Bool}:
  acyc => +hc => Reach.put_acyclic.at(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    ~refl,
    ~sound,
    ~live,
    ~W,
    ~put,
    ~agree,
    Reach.in(~A, ~V, ~same, ~succ, ~nodes, put(g)(c)(w), x, x),
    x,
    g,
    c,
    w,
    acyc,
    hc
  )({==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a list that closes a cycle keeps each and/or as one value, for the proofs to split on
# a path from no nodes leads nowhere
def Reach.path_empty(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ps: List<&2, A>,
  g: V,
  m: A
) -> {Reach.path(~A, ~V, ~same, ~succ, ps, [], g, m) == False{}: Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.closes_split, once the rest is split
def Reach.closes_split.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  g: V,
  c: A,
  x: A,
  r: List<&2, A>,
  w: &pre: List<
    &2,
    A> -> &y: A -> &post: List<
    &2,
    A> -> {
    r == List.append(&2, A, pre, y <> post): List<&2, A>
  }
    & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool}
) -> &pre:
  List<
    &2,
    A> -> &y: A -> &post: List<
    &2,
    A> -> {
    x <> r == List.append(&2, A, pre, y <> post): List<&2, A>
  }
    & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool}:
  match w:
    case (pre, (y, (post, (e1, e2)))):
      (
        x <> pre,
        (
          y,
          (
            post,
            (
              Equal.cong(
                List<&2, A>,
                List<&2, A>,
                z => x <> z,
                r,
                List.append(&2, A, pre, y <> post),
                e1
              ),
              e2
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Reach.closes_split at the first node x, by whether it closes a cycle (hit)
def Reach.closes_split.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  hit: Bool,
  g: V,
  c: A,
  x: A,
  r: List<&2, A>,
  ih: {
    Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r) == True{}: Bool
  } -> &pre: List<
    &2,
    A> -> &y: A -> &post: List<
    &2,
    A> -> {
    r == List.append(&2, A, pre, y <> post): List<&2, A>
  }
    & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool}
) -> {
  Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c)) == hit: Bool
} -> {Bool.or(hit, Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, r)) == True{}: Bool} -> &pre:
  List<
    &2,
    A> -> &y: A -> &post: List<
    &2,
    A> -> {
    x <> r == List.append(&2, A, pre, y <> post): List<&2, A>
  }
    & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool}:
  match hit:
    case True{}:
      e => h => ([], (x, (r, ({==}, e))))
    case False{}:
      e => h => Reach.closes_split.cons(~A, ~V, ~same, ~succ, ~nodes, g, c, x, r, ih(h))

# a list that closes a cycle has a node that does, with the nodes before and
# after it
def Reach.closes_split(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  +g: V,
  +c: A,
  ys: List<&2, A>
) -> {Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, ys) == True{}: Bool} -> &pre:
  List<
    &2,
    A> -> &y: A -> &post: List<
    &2,
    A> -> {
    ys == List.append(&2, A, pre, y <> post): List<&2, A>
  }
    & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool}:
  match ys:
    case Nil{}:
      h => Empty.absurd(
        &pre: List<
          &2,
          A> -> &y: A -> &post: List<
          &2,
          A> -> {
          [] == List.append(&2, A, pre, y <> post): List<&2, A>
        }
          & {Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      Reach.closes_split.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~nodes,
        Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c)),
        g,
        c,
        x,
        r,
        Reach.closes_split(~A, ~V, ~same, ~succ, ~nodes, g, c, r)
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a node that closes a cycle makes every list with it close one
def Reach.closes_middle(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  +g: V,
  +c: A,
  pre: List<&2, A>,
  y: A,
  post: List<&2, A>
) -> {
  Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)) == True{}: Bool
} -> {
  Reach.closes(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    g,
    c,
    List.append(&2, A, pre, y <> post)
  )
    == True{}: Bool
}:
  match pre:
    case Nil{}:
      h =>
        %Equal.sym(
          Bool,
          Bool.or(same(y, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, y, c)),
          True{},
          h
        ): {Bool.or(_, Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, post)) == True{}: Bool}
        {==}
    case Con{+x, r}:
      h =>
        %Equal.sym(
          Bool,
          Reach.closes(~A, ~V, ~same, ~succ, ~nodes, g, c, List.append(&2, A, r, y <> post)),
          True{},
          Reach.closes_middle(~A, ~V, ~same, ~succ, ~nodes, g, c, r, y, post)(h)
        ): {
          Bool.or(
            Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c)),
            _
          )
            == True{}: Bool
        }
        Bools.Bool.or_true_right(
          Bool.or(same(x, c), Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, c))
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
