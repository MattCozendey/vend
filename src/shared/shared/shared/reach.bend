import Base
import ./shared/shared.bend as Shared
import ./shared/crit.bend as Crits

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
    # bend-lint: expect-begin bend-lint-rules/language/unneeded_plus@hint -- a succ that uses its node twice needs it: without the +, bend refuses that instance (x consumed more than once)
    case Con{+x, r}:
    # bend-lint: expect-end bend-lint-rules/language/unneeded_plus@hint
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
      List.contains(~A, ~same, xs, m)
    case 1n+e:
      Bool.or(
        List.contains(~A, ~same, xs, m),
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
      List.contains(~A, ~same, xs, m)
    case Con{+p, r}:
      Bool.and(
        List.contains(~A, ~same, xs, p),
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
      Bool.and(Bool.not(List.contains(~A, ~same, r, p)), Reach.distinct(~A, ~same, r))

# the nodes of ps after the first that is p
def Reach.after(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>, +p: A) -> List<&2, A>:
  match ps:
    case Nil{}:
      []
    case Con{x, +r}:
      Shared.Bool.when(List<&2, A>, same(x, p), u => r, u => Reach.after(~A, ~same, r, p))

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
    List.contains(~A, ~same, r, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool}
) -> &y:
  A -> {
    List.contains(~A, ~same, x <> r, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match w:
    case (+y, (h1, h2)):
      (y, (Shared.List.contains_cons(~A, ~same, x, r, y)(h1), h2))

# Reach.next_found at the first node x of xs, by whether q is its successor
# (hit)
def Reach.next_found.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  g: V,
  q: A,
  ih: {
    List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q) == True{}: Bool
  } -> &y: A -> {
    List.contains(~A, ~same, r, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool}
) -> {
  List.contains(~A, ~same, succ(g)(x), q) == hit: Bool
} -> {
  Bool.or(hit, List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q)) == True{}: Bool
} -> &y:
  A -> {
    List.contains(~A, ~same, x <> r, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match hit:
    case True{}:
      +e => +h =>
        (x, ((
              %Equal.sym(Bool, same(x, x), True{}, Shared.Eq.refl(~A, ~same, laws, x)): {List.any.if(u => List.contains(~A, ~same, r, x), _) == True{}: Bool}
              {==}), e))
    case False{}:
      +e => +h => Reach.next_found.cons(~A, ~V, ~same, ~succ, x, r, g, q, ih(h))

# a node q of the next level is a successor of a node of xs
def Reach.next_found(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +g: V,
  +q: A
) -> {List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q) == True{}: Bool} -> &y:
  A -> {
    List.contains(~A, ~same, xs, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool}:
  match xs:
    case Nil{}:
      +h => Empty.absurd(
        &y: A -> {
          List.contains(~A, ~same, [], y) == True{}: Bool
        }
          & {List.contains(~A, ~same, succ(g)(y), q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      +h =>
        Reach.next_found.at(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          List.contains(~A, ~same, succ(g)(x), q),
          x,
          r,
          g,
          q,
          Reach.next_found(~A, ~V, ~same, ~succ, ~laws, r, g, q)
        )({==})((
            %Shared.List.contains_append(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g), q): {_ == True{}: Bool}
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
    List.contains(~A, ~same, xs, y) == True{}: Bool
  }
    & {List.contains(~A, ~same, succ(g)(y), p) == True{}: Bool}
) -> &y:
  A -> {
    List.contains(~A, ~same, xs, y) == True{}: Bool
  }
    & {Reach.path(~A, ~V, ~same, ~succ, p <> r, succ(g)(y), g, m) == True{}: Bool}:
  match w:
    case (y, (h1, h2)):
      (y, (h1, (
            %Equal.sym(Bool, List.contains(~A, ~same, succ(g)(y), p), True{}, h2): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)) == True{}: Bool}
            hr)))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a path from the next level starts at a successor of a node of xs
def Reach.path_step(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +ps: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool
} -> &y:
  A -> {
    List.contains(~A, ~same, xs, y) == True{}: Bool
  }
    & {Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => Reach.next_found(~A, ~V, ~same, ~succ, ~laws, xs, g, m)(h)
    case Con{+p, +r}:
      +contains1 = List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), p)
      path1 = Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
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
        Shared.Bool.and_true_right(contains1, path1)(h),
        Reach.next_found(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          xs,
          g,
          p
        )(Shared.Bool.and_true_left(contains1, path1)(h))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
    List.contains(~A, ~same, xs, y) == True{}: Bool
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
            %Equal.sym(Bool, List.contains(~A, ~same, xs, y), True{}, h1): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m)) == True{}: Bool}
            h2), hf))

# Reach.go_path below the first level, once a path from the next level is found
def Reach.go_path.lift(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
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
        Reach.path_step(~A, ~V, ~same, ~succ, ~laws, xs, ps, g, m)(hp)
      )

# Reach.go_path one level down, by whether m is in the first level (hit)
def Reach.go_path.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
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
  List.contains(~A, ~same, xs, m) == hit: Bool
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
      +he => +h => Reach.go_path.lift(~A, ~V, ~same, ~succ, ~laws, xs, e, g, m, ih(h))

# a search that finds m has a path to m, no longer than the search is deep
def Reach.go_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
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
        ~laws,
        List.contains(~A, ~same, xs, m),
        e,
        xs,
        g,
        m,
        Reach.go_path(~A, ~V, ~same, ~succ, ~laws, e, Reach.next(~A, ~V, ~succ, xs, g), g, m)
      )({==})(h)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.found_sub at the first node x of xs, by whether it is p (hit)
def Reach.found_sub.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  p: A,
  +q: A,
  +g: V,
  ih: {
    List.contains(~A, ~same, r, p) == True{}: Bool
  } -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, r, g), q) == True{}: Bool}
) -> {
  same(x, p) == hit: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
} -> {
  List.contains(
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
        +next1 = Reach.next(~A, ~V, ~succ, r, g)
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, List.append(&2, A, succ(g)(x), next1), q),
          Bool.or(List.contains(~A, ~same, succ(g)(x), q), List.contains(~A, ~same, next1, q)),
          Shared.List.contains_append(~A, ~same, succ(g)(x), next1, q)
        ): {_ == True{}: Bool}
        %Equal.sym(
          A,
          x,
          p,
          Shared.Eq.sound(~A, ~same, laws, x)(p)(he)
        ): {
          Bool.or(
            List.contains(~A, ~same, succ(g)(_), q),
            List.contains(~A, ~same, next1, q)
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, succ(g)(p), q),
          True{},
          hq
        ): {Bool.or(_, List.contains(~A, ~same, next1, q)) == True{}: Bool}
        {==}
    case False{}:
      +he => +h => +hq =>
        +next1 = Reach.next(~A, ~V, ~succ, r, g)
        +contains1 = List.contains(~A, ~same, succ(g)(x), q)
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, List.append(&2, A, succ(g)(x), next1), q),
          Bool.or(contains1, List.contains(~A, ~same, next1, q)),
          Shared.List.contains_append(~A, ~same, succ(g)(x), next1, q)
        ): {_ == True{}: Bool}
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, next1, q),
          True{},
          ih(h)(hq)
        ): {Bool.or(contains1, _) == True{}: Bool}
        Shared.Bool.or_true_right(contains1)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a successor q of a node p of xs is in the next level
def Reach.found_sub(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +p: A,
  +q: A,
  +g: V
) -> {
  List.contains(~A, ~same, xs, p) == True{}: Bool
} -> {
  List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
} -> {List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q) == True{}: Bool}:
  match xs:
    case Nil{}:
      +h => +hq => Empty.absurd(
        {List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, [], g), q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      +h => Reach.found_sub.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        same(x, p),
        x,
        r,
        p,
        q,
        g,
        Reach.found_sub(~A, ~V, ~same, ~succ, ~laws, r, p, q, g)
      )({==})(h)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a path from a successor of a node p of xs is a path from the next level
def Reach.path_sub(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +p: A,
  +r: List<&2, A>,
  +g: V,
  m: A
) -> {
  List.contains(~A, ~same, xs, p) == True{}: Bool
} -> {
  Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m) == True{}: Bool
} -> {Reach.path(~A, ~V, ~same, ~succ, r, Reach.next(~A, ~V, ~succ, xs, g), g, m) == True{}: Bool}:
  match r:
    case Nil{}:
      +hp => +h => Reach.found_sub(~A, ~V, ~same, ~succ, ~laws, xs, p, m, g)(hp)(h)
    case Con{+q, r2}:
      +hp => +h =>
        +path1 = Reach.path(~A, ~V, ~same, ~succ, r2, succ(g)(q), g, m)
        +contains1 = List.contains(~A, ~same, succ(g)(p), q)
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, Reach.next(~A, ~V, ~succ, xs, g), q),
          True{},
          Reach.found_sub(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            xs,
            p,
            q,
            g
          )(hp)(Shared.Bool.and_true_left(contains1, path1)(h))
        ): {Bool.and(_, path1) == True{}: Bool}
        Shared.Bool.and_true_right(contains1, path1)(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a path no longer than f makes a search f levels deep find its end
def Reach.path_go(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
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
          List.contains(~A, ~same, xs, m),
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
        +path1 = Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
        +next1 = Reach.next(~A, ~V, ~succ, xs, g)
        +contains1 = List.contains(~A, ~same, xs, p)
        +contains2 = List.contains(~A, ~same, xs, m)
        %Equal.sym(
          Bool,
          Reach.go(~A, ~V, ~same, ~succ, e, next1, g, m),
          True{},
          Reach.path_go(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            r,
            e,
            next1,
            g,
            m
          )(
            Reach.path_sub(
              ~A,
              ~V,
              ~same,
              ~succ,
              ~laws,
              xs,
              p,
              r,
              g,
              m
            )(
              Shared.Bool.and_true_left(contains1, path1)(h)
            )(Shared.Bool.and_true_right(contains1, path1)(h))
          )(hf)
        ): {Bool.or(contains2, _) == True{}: Bool}
        Shared.Bool.or_true_right(contains2)

# a path to h, then a path from h to m, is a path to m
def Reach.path_append(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +a: List<&2, A>,
  xs: List<&2, A>,
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
          List.contains(~A, ~same, xs, h),
          True{},
          ha
        ): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, b, succ(g)(h), g, m)) == True{}: Bool}
        hb
    case Con{+p, +r}:
      +ha => +hb =>
        +path1 = Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, h)
        +contains1 = List.contains(~A, ~same, xs, p)
        %Equal.sym(
          Bool,
          contains1,
          True{},
          Shared.Bool.and_true_left(contains1, path1)(ha)
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
        )(Shared.Bool.and_true_right(contains1, path1)(ha))(hb)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a path starts in its level
def Reach.path_first(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ps: List<&2, A>,
  ys: List<&2, A>,
  g: V,
  m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {List.contains(~A, ~same, ys, Reach.first(A, ps, m)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => h
    case Con{p, r}:
      +h => Shared.Bool.and_true_left(
        List.contains(~A, ~same, ys, p),
        Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
      )(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the nodes of a path have successors, so they are nodes of the graph
def Reach.path_within(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
  +ps: List<&2, A>,
  ys: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {Shared.List.within(~A, ~same, ps, nodes(g)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => {==}
    case Con{+p, +r}:
      +h =>
        +path1 = Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
        +contains1 = List.contains(~A, ~same, ys, p)
        hf = Reach.path_first(
          ~A,
          ~V,
          ~same,
          ~succ,
          r,
          succ(g)(p),
          g,
          m
        )(Shared.Bool.and_true_right(contains1, path1)(h))
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, nodes(g), p),
          True{},
          live(g)(p)(Reach.first(A, r, m))(hf)
        ): {Bool.and(_, Shared.List.within(~A, ~same, r, nodes(g))) == True{}: Bool}
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
        )(Shared.Bool.and_true_right(contains1, path1)(h))

# Reach.after_path at the first node x of rs, by whether it is p (hit)
def Reach.after_path.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  +x: A,
  r: List<&2, A>,
  p: A,
  ys: List<&2, A>,
  +g: V,
  m: A,
  ih: {
    List.contains(~A, ~same, r, p) == True{}: Bool
  } -> {
    Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m) == True{}: Bool
  } -> {
    Reach.path(~A, ~V, ~same, ~succ, Reach.after(~A, ~same, r, p), succ(g)(p), g, m) == True{}: Bool
  }
) -> {
  same(x, p) == hit: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  Bool.and(
    List.contains(~A, ~same, ys, x),
    Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
  )
    == True{}: Bool
} -> {
  Reach.path(
    ~A,
    ~V,
    ~same,
    ~succ,
    Shared.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p)),
    succ(g)(p),
    g,
    m
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +hf => +hp =>
        %Shared.Eq.sound(
          ~A,
          ~same,
          laws,
          x
        )(p)(he): {Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(_), g, m) == True{}: Bool}
        Shared.Bool.and_true_right(
          List.contains(~A, ~same, ys, x),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
        )(hp)
    case False{}:
      +he => +hf => +hp => ih(
        hf
      )(
        Shared.Bool.and_true_right(
          List.contains(~A, ~same, ys, x),
          Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(x), g, m)
        )(hp)
      )

# what follows a node p of a path is a path from p's successors
def Reach.after_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +rs: List<&2, A>,
  +p: A,
  ys: List<&2, A>,
  +g: V,
  +m: A
) -> {
  List.contains(~A, ~same, rs, p) == True{}: Bool
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
        ~laws,
        same(x, p),
        x,
        r,
        p,
        ys,
        g,
        m,
        Reach.after_path(~A, ~V, ~same, ~succ, ~laws, r, p, succ(g)(x), g, m)
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
  Bool.and(Bool.not(List.contains(~A, ~same, r, x)), Reach.distinct(~A, ~same, r)) == True{}: Bool
} -> {
  Reach.distinct(
    ~A,
    ~same,
    Shared.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p))
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +hd => Shared.Bool.and_true_right(
        Bool.not(List.contains(~A, ~same, r, x)),
        Reach.distinct(~A, ~same, r)
      )(hd)
    case False{}:
      +he => +hd => ih(
        Shared.Bool.and_true_right(
          Bool.not(List.contains(~A, ~same, r, x)),
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
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  +x: A,
  +r: List<&2, A>,
  p: A,
  ih: {
    Reach.distinct(~A, ~same, r) == True{}: Bool
  } -> {
    List.contains(~A, ~same, r, p) == True{}: Bool
  } -> {List.contains(~A, ~same, Reach.after(~A, ~same, r, p), p) == False{}: Bool}
) -> {
  same(x, p) == hit: Bool
} -> {
  Bool.and(Bool.not(List.contains(~A, ~same, r, x)), Reach.distinct(~A, ~same, r)) == True{}: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, p), hit) == True{}: Bool
} -> {
  List.contains(
    ~A,
    ~same,
    Shared.Bool.when(List<&2, A>, hit, u => r, u => Reach.after(~A, ~same, r, p)),
    p
  )
    == False{}: Bool
}:
  match hit:
    case True{}:
      +he => +hd => +hf =>
        +contains1 = List.contains(~A, ~same, r, x)
        %Shared.Eq.sound(
          ~A,
          ~same,
          laws,
          x
        )(p)(he): {List.contains(~A, ~same, r, _) == False{}: Bool}
        Shared.Bool.not_true(
          contains1
        )(Shared.Bool.and_true_left(Bool.not(contains1), Reach.distinct(~A, ~same, r))(hd))
    case False{}:
      +he => +hd => +hf => ih(
        Shared.Bool.and_true_right(
          Bool.not(List.contains(~A, ~same, r, x)),
          Reach.distinct(~A, ~same, r)
        )(hd)
      )(hf)

# p does not come again after its first place in a path that visits each node
# once
def Reach.after_free(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +rs: List<&2, A>,
  +p: A
) -> {
  Reach.distinct(~A, ~same, rs) == True{}: Bool
} -> {
  List.contains(~A, ~same, rs, p) == True{}: Bool
} -> {List.contains(~A, ~same, Reach.after(~A, ~same, rs, p), p) == False{}: Bool}:
  match rs:
    case Nil{}:
      +hd => +hf => Empty.absurd(
        {List.contains(~A, ~same, [], p) == False{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+x, +r}:
      Reach.after_free.at(
        ~A,
        ~same,
        ~laws,
        same(x, p),
        x,
        r,
        p,
        Reach.after_free(~A, ~same, ~laws, r, p)
      )({==})

# Reach.shorten after its first node p, by whether p comes again (hit)
def Reach.shorten.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  xs: List<&2, A>,
  +p: A,
  +rs: List<&2, A>,
  +g: V,
  m: A,
  hx: {List.contains(~A, ~same, xs, p) == True{}: Bool},
  hp: {Reach.path(~A, ~V, ~same, ~succ, rs, succ(g)(p), g, m) == True{}: Bool},
  +hd: {Reach.distinct(~A, ~same, rs) == True{}: Bool}
) -> {List.contains(~A, ~same, rs, p) == hit: Bool} -> &qs:
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
              %Equal.sym(Bool, List.contains(~A, ~same, xs, p), True{}, hx): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, rs, succ(g)(p), g, m)) == True{}: Bool}
              hp), (
              %Equal.sym(Bool, List.contains(~A, ~same, rs, p), False{}, he): {Bool.and(Bool.not(_), Reach.distinct(~A, ~same, rs)) == True{}: Bool}
              hd)))
    case True{}:
      +he =>
        +after1 = Reach.after(~A, ~same, rs, p)
        (p <> after1, ((
              %Equal.sym(Bool, List.contains(~A, ~same, xs, p), True{}, hx): {Bool.and(_, Reach.path(~A, ~V, ~same, ~succ, after1, succ(g)(p), g, m)) == True{}: Bool}
              Reach.after_path(~A, ~V, ~same, ~succ, ~laws, rs, p, succ(g)(p), g, m)(he)(hp)), (
              %Equal.sym(Bool, List.contains(~A, ~same, after1, p), False{}, Reach.after_free(~A, ~same, ~laws, rs, p)(hd)(he)): {Bool.and(Bool.not(_), Reach.distinct(~A, ~same, after1)) == True{}: Bool}
              Reach.after_distinct(~A, ~same, rs, p)(hd))))

# Reach.shorten after its first node p, once the rest is cut
def Reach.shorten.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +p: A,
  g: V,
  m: A,
  hx: {List.contains(~A, ~same, xs, p) == True{}: Bool},
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
        ~laws,
        List.contains(~A, ~same, rs, p),
        xs,
        p,
        rs,
        g,
        m,
        hx,
        hp,
        hd
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a path can be cut down to one that visits each node once
def Reach.shorten(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
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
      path1 = Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
      +contains1 = List.contains(~A, ~same, xs, p)
      +h => Reach.shorten.cons(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        xs,
        p,
        g,
        m,
        Shared.Bool.and_true_left(contains1, path1)(h),
        Reach.shorten(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          r,
          succ(g)(p),
          g,
          m
        )(Shared.Bool.and_true_right(contains1, path1)(h))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
    List.contains(~A, ~same, r, p) == True{}: Bool
  } -> {
    Nat.is_le(
      1n+List.length(&2, A, Shared.List.remove(~A, ~same, r, p)),
      List.length(&2, A, r)
    )
      == True{}: Bool
  }
) -> {
  List.any.if(u => List.contains(~A, ~same, r, p), hit) == True{}: Bool
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
  List.contains(~A, ~same, ks, p) == True{}: Bool
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
  ~laws: Shared.Eq.Laws(A, same),
  +hk: Bool,
  +hq: Bool,
  k: A,
  r: List<&2, A>,
  p: A,
  q: A,
  ih: {
    List.contains(~A, ~same, r, q) == True{}: Bool
  } -> {
    same(q, p) == False{}: Bool
  } -> {List.contains(~A, ~same, Shared.List.remove(~A, ~same, r, p), q) == True{}: Bool}
) -> {
  same(k, p) == hk: Bool
} -> {
  same(k, q) == hq: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, q), hq) == True{}: Bool
} -> {
  same(q, p) == False{}: Bool
} -> {
  List.contains(
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
          {List.contains(~A, ~same, Shared.List.remove(~A, ~same, r, p), q) == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(Bool, False{}, same(k, p), True{}, Equal.sym(Bool, same(k, p), False{}, (
                  %Equal.sym(A, k, q, Shared.Eq.sound(~A, ~same, laws, k)(q)(eq)): {same(_, p) == False{}: Bool}
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
            u => List.contains(~A, ~same, Shared.List.remove(~A, ~same, r, p), q),
            _
          )
            == True{}: Bool
        }
        {==}
    case False{} False{}:
      +ek => +eq => +h => +hn =>
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, Shared.List.remove(~A, ~same, r, p), q),
          True{},
          ih(h)(hn)
        ): {List.any.if(u => _, same(k, q)) == True{}: Bool}
        Shared.List.any.if_true(same(k, q))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# dropping the nodes that are p keeps the others
def Reach.drop_keep(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ks: List<&2, A>,
  +p: A,
  +q: A
) -> {
  List.contains(~A, ~same, ks, q) == True{}: Bool
} -> {
  same(q, p) == False{}: Bool
} -> {List.contains(~A, ~same, Shared.List.remove(~A, ~same, ks, p), q) == True{}: Bool}:
  match ks:
    case Nil{}:
      +h => +hn => Empty.absurd(
        {List.contains(~A, ~same, [], q) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+k, +r}:
      Reach.drop_keep.at(
        ~A,
        ~same,
        ~laws,
        same(k, p),
        same(k, q),
        k,
        r,
        p,
        q,
        Reach.drop_keep(~A, ~same, ~laws, r, p, q)
      )({==})({==})

# the nodes of ps, none of them p, stay in ks without p
def Reach.within_drop(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +p: A
) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  List.contains(~A, ~same, ps, p) == False{}: Bool
} -> {Shared.List.within(~A, ~same, ps, Shared.List.remove(~A, ~same, ks, p)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hw => +hn => {==}
    case Con{+q, +r}:
      +hw => +hn =>
        +remove1 = Shared.List.remove(~A, ~same, ks, p)
        +contains1 = List.contains(~A, ~same, ks, q)
        +within1 = Shared.List.within(~A, ~same, r, ks)
        +contains2 = List.contains(~A, ~same, r, p)
        %Equal.sym(
          Bool,
          List.contains(~A, ~same, remove1, q),
          True{},
          Reach.drop_keep(
            ~A,
            ~same,
            ~laws,
            ks,
            p,
            q
          )(
            Shared.Bool.and_true_left(contains1, within1)(hw)
          )(Shared.List.any.if_false_hit(same(q, p), u => contains2)(hn))
        ): {Bool.and(_, Shared.List.within(~A, ~same, r, remove1)) == True{}: Bool}
        Reach.within_drop(
          ~A,
          ~same,
          ~laws,
          r,
          ks,
          p
        )(
          Shared.Bool.and_true_right(contains1, within1)(hw)
        )(Shared.List.any.if_false_rest(same(q, p), u => contains2)(hn))

# a path that visits each node of ks at most once has no more nodes than ks
def Reach.fits_nodes(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +ks: List<&2, A>
) -> {
  Reach.distinct(~A, ~same, ps) == True{}: Bool
} -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {Reach.fits(A, ps, List.length(&2, A, ks)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hd => +hw => {==}
    case Con{+p, +r}:
      +hd => +hw =>
        +contains1 = List.contains(~A, ~same, r, p)
        +remove1 = Shared.List.remove(~A, ~same, ks, p)
        +contains2 = List.contains(~A, ~same, ks, p)
        +within1 = Shared.List.within(~A, ~same, r, ks)
        +distinct1 = Reach.distinct(~A, ~same, r)
        Reach.fits_le(
          A,
          p <> r,
          1n+List.length(&2, A, remove1),
          List.length(&2, A, ks)
        )(
          Reach.fits_nodes(
            ~A,
            ~same,
            ~laws,
            r,
            remove1
          )(
            Shared.Bool.and_true_right(Bool.not(contains1), distinct1)(hd)
          )(
            Reach.within_drop(
              ~A,
              ~same,
              ~laws,
              r,
              ks,
              p
            )(
              Shared.Bool.and_true_right(contains2, within1)(hw)
            )(
              Shared.Bool.not_true(
                contains1
              )(Shared.Bool.and_true_left(Bool.not(contains1), distinct1)(hd))
            )
          )
        )(Reach.drop_lt(~A, ~same, ks, p)(Shared.Bool.and_true_left(contains2, within1)(hw)))

# Transitivity
# ------------

# Reach.in_through, once both paths are cut to visit each node once
def Reach.in_through.fin(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
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
        ~laws,
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
          ~laws,
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
  ~laws: Shared.Eq.Laws(A, same),
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
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
        ~laws,
        ~live,
        g,
        x,
        m,
        Reach.shorten(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
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
  ~laws: Shared.Eq.Laws(A, same),
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
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
      Reach.in_through.two(~A, ~V, ~same, ~succ, ~nodes, ~laws, ~live, g, x, h, m, ps1, h1, w2)

# what is inside a node h that is inside x is inside x: what a search finds
# is reachable at any depth, through any node it finds
law Reach.in_through:
  for ~A: Data
  for ~V: Data
  for ~same: A -> A -> Bool
  for ~succ: V -> A -> List<&2, A>
  for ~nodes: V -> List<&2, A>
  for ~laws: Shared.Eq.Laws(A, same)
  for ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool}
  for +g: V
  for +x: A
  for +h: A
  for +m: A
  {
    Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, h) == True{}: Bool
  } -> {
    Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, h, m) == True{}: Bool
  } -> {Reach.in(~A, ~V, ~same, ~succ, ~nodes, g, x, m) == True{}: Bool}

def Reach.in_through(ty, gt, same, succ, nodes, laws, live, g, x, h, m):
  +length1 = List.length(&2, ty, nodes(g))
  +a => +b => Reach.in_through.one(
    ~ty,
    ~gt,
    ~same,
    ~succ,
    ~nodes,
    ~laws,
    ~live,
    g,
    x,
    h,
    m,
    Reach.go_path(~ty, ~gt, ~same, ~succ, ~laws, length1, succ(g)(x), g, h)(a),
    Reach.go_path(~ty, ~gt, ~same, ~succ, ~laws, length1, succ(g)(h), g, m)(b)
  )

# Fast search
# -----------
# Reach.go visits a node once for each path to it, so a level can double at
# each step. Reach.fill keeps the nodes that it saw in a trie, and visits each
# node once. Its nodes are trie keys: two of them are the same exactly when
# they are equal.

# the key of a node: the node itself
def Reach.key(k: List<&2, U32>) -> List<&2, U32>:
  k

# seen, with each node that a search f levels deep finds from the level ws
def Reach.fill(
  ~V: Data,
  ~succ: V -> List<&2, U32> -> List<&2, List<&2, U32>>,
  f: Nat,
  ws: List<&2, List<&2, U32>>,
  +g: V,
  +seen: Crits.Dict(Unit)
) -> Crits.Dict(Unit):
  match f ws:
    case 0n xs:
      Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, xs, seen)
    case 1n+e Nil{}:
      seen
    case 1n+e Con{w, r}:
      +ys = Crits.Dict.unique(~List<&2, U32>, ~Reach.key, w <> r, seen)
      Reach.fill(
        ~V,
        ~succ,
        e,
        Reach.next(~List<&2, U32>, ~V, ~succ, ys, g),
        g,
        Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ys, seen)
      )

# each successor of x, and each successor of one, at any depth: one search
# answers Reach.in for every m
def Reach.all(
  ~V: Data,
  ~succ: V -> List<&2, U32> -> List<&2, List<&2, U32>>,
  ~nodes: V -> List<&2, List<&2, U32>>,
  +g: V,
  x: List<&2, U32>
) -> Crits.Dict(Unit):
  Reach.fill(
    ~V,
    ~succ,
    List.length(&2, List<&2, U32>, nodes(g)),
    succ(g)(x),
    g,
    Crits.Dict.new(~Unit)
  )

# Reach.within_in at the first node q of ps, by whether it is p (hit)
def Reach.within_in.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  q: A,
  r: List<&2, A>,
  ks: List<&2, A>,
  p: A,
  hq: {List.contains(~A, ~same, ks, q) == True{}: Bool},
  ih: {
    List.contains(~A, ~same, r, p) == True{}: Bool
  } -> {List.contains(~A, ~same, ks, p) == True{}: Bool}
) -> {
  same(q, p) == hit: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, p), hit) == True{}: Bool
} -> {List.contains(~A, ~same, ks, p) == True{}: Bool}:
  match hit:
    case True{}:
      +he => +h =>
        %Shared.Eq.sound(
          ~A,
          ~same,
          laws,
          q
        )(p)(he): {List.contains(~A, ~same, ks, _) == True{}: Bool}
        hq
    case False{}:
      +he => +h => ih(h)

# a node of ps is in ks, when every node of ps is
def Reach.within_in(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +p: A
) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  List.contains(~A, ~same, ps, p) == True{}: Bool
} -> {List.contains(~A, ~same, ks, p) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hw => +hp => Empty.absurd(
        {List.contains(~A, ~same, ks, p) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case Con{+q, +r}:
      +hw => Reach.within_in.at(
        ~A,
        ~same,
        ~laws,
        same(q, p),
        q,
        r,
        ks,
        p,
        Shared.Bool.and_true_left(
          List.contains(~A, ~same, ks, q),
          Shared.List.within(~A, ~same, r, ks)
        )(hw),
        Reach.within_in(
          ~A,
          ~same,
          ~laws,
          r,
          ks,
          p
        )(
          Shared.Bool.and_true_right(
            List.contains(~A, ~same, ks, q),
            Shared.List.within(~A, ~same, r, ks)
          )(hw)
        )
      )({==})

# Reach.within_out once it is known if p is in ps (b)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Reach.within_out.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  ps: List<&2, A>,
  ks: List<&2, A>,
  p: A,
  b: Bool,
  hw: {Shared.List.within(~A, ~same, ps, ks) == True{}: Bool},
  hk: {List.contains(~A, ~same, ks, p) == False{}: Bool}
) -> {List.contains(~A, ~same, ps, p) == b: Bool} -> {b == False{}: Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            List.contains(~A, ~same, ks, p),
            True{},
            Equal.sym(Bool, List.contains(~A, ~same, ks, p), False{}, hk),
            Reach.within_in(~A, ~same, ~laws, ps, ks, p)(hw)(e)
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a node that ks lacks is not in ps, when every node of ps is in ks
def Reach.within_out(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  ks: List<&2, A>,
  +p: A,
  hw: {Shared.List.within(~A, ~same, ps, ks) == True{}: Bool},
  hk: {List.contains(~A, ~same, ks, p) == False{}: Bool}
) -> {List.contains(~A, ~same, ps, p) == False{}: Bool}:
  Reach.within_out.at(~A, ~same, ~laws, ps, ks, p, List.contains(~A, ~same, ps, p), hw, hk)({==})

# ps is within js, when it is within ks and ks is within js
def Reach.within_trans(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +js: List<&2, A>
) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  Shared.List.within(~A, ~same, ks, js) == True{}: Bool
} -> {Shared.List.within(~A, ~same, ps, js) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h1 => +h2 => {==}
    case Con{+p, +r}:
      +h1 => +h2 =>
        +contains1 = List.contains(~A, ~same, ks, p)
        +within1 = Shared.List.within(~A, ~same, r, ks)
        Shared.Bool.and_both(
          List.contains(~A, ~same, js, p),
          Shared.List.within(~A, ~same, r, js)
        )(
          Reach.within_in(
            ~A,
            ~same,
            ~laws,
            ks,
            js,
            p
          )(h2)(Shared.Bool.and_true_left(contains1, within1)(h1))
        )(
          Reach.within_trans(
            ~A,
            ~same,
            ~laws,
            r,
            ks,
            js
          )(Shared.Bool.and_true_right(contains1, within1)(h1))(h2)
        )

# ps and then qs is within ks, when each is
def Reach.within_both(
  ~A: Data,
  ~same: A -> A -> Bool,
  +ps: List<&2, A>,
  +qs: List<&2, A>,
  +ks: List<&2, A>
) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  Shared.List.within(~A, ~same, qs, ks) == True{}: Bool
} -> {Shared.List.within(~A, ~same, List.append(&2, A, ps, qs), ks) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h1 => +h2 => h2
    case Con{p, +r}:
      +h1 => +h2 =>
        +contains1 = List.contains(~A, ~same, ks, p)
        +within1 = Shared.List.within(~A, ~same, r, ks)
        Shared.Bool.and_both(
          contains1,
          Shared.List.within(~A, ~same, List.append(&2, A, r, qs), ks)
        )(
          Shared.Bool.and_true_left(contains1, within1)(h1)
        )(
          Reach.within_both(
            ~A,
            ~same,
            r,
            qs,
            ks
          )(Shared.Bool.and_true_right(contains1, within1)(h1))(h2)
        )

# what is within ks is within ks and then js
def Reach.within_left(
  ~A: Data,
  ~same: A -> A -> Bool,
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +js: List<&2, A>
) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {Shared.List.within(~A, ~same, ps, List.append(&2, A, ks, js)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => {==}
    case Con{+p, +r}:
      +h =>
        +contains1 = List.contains(~A, ~same, ks, p)
        +within1 = Shared.List.within(~A, ~same, r, ks)
        Shared.Bool.and_both(
          List.contains(~A, ~same, List.append(&2, A, ks, js), p),
          Shared.List.within(~A, ~same, r, List.append(&2, A, ks, js))
        )(
          Shared.List.contains_left(
            ~A,
            ~same,
            ks,
            js,
            p,
            Shared.Bool.and_true_left(contains1, within1)(h)
          )
        )(
          Reach.within_left(~A, ~same, r, ks, js)(Shared.Bool.and_true_right(contains1, within1)(h))
        )

# what is within js is within ks and then js
def Reach.within_right(
  ~A: Data,
  ~same: A -> A -> Bool,
  +ps: List<&2, A>,
  +ks: List<&2, A>,
  +js: List<&2, A>
) -> {
  Shared.List.within(~A, ~same, ps, js) == True{}: Bool
} -> {Shared.List.within(~A, ~same, ps, List.append(&2, A, ks, js)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h => {==}
    case Con{+p, +r}:
      +h =>
        +contains1 = List.contains(~A, ~same, js, p)
        +within1 = Shared.List.within(~A, ~same, r, js)
        Shared.Bool.and_both(
          List.contains(~A, ~same, List.append(&2, A, ks, js), p),
          Shared.List.within(~A, ~same, r, List.append(&2, A, ks, js))
        )(
          Shared.List.contains_right(
            ~A,
            ~same,
            ks,
            js,
            p,
            Shared.Bool.and_true_left(contains1, within1)(h)
          )
        )(
          Reach.within_right(
            ~A,
            ~same,
            r,
            ks,
            js
          )(Shared.Bool.and_true_right(contains1, within1)(h))
        )

# a list is within itself
def Reach.within_self(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>
) -> {Shared.List.within(~A, ~same, ps, ps) == True{}: Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %Equal.sym(
        Bool,
        same(p, p),
        True{},
        Shared.Eq.refl(~A, ~same, laws, p)
      ): {
        Bool.and(
          List.any.if(u => List.contains(~A, ~same, r, p), _),
          Shared.List.within(~A, ~same, r, p <> r)
        )
          == True{}: Bool
      }
      Reach.within_right(~A, ~same, r, [p], r)(Reach.within_self(~A, ~same, ~laws, r))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the next level of xs and then ys is the next of xs, and then the next of ys
def Reach.next_append(
  ~A: Data,
  ~V: Data,
  ~succ: V -> A -> List<&2, A>,
  +xs: List<&2, A>,
  +ys: List<&2, A>,
  +g: V
) -> {
  Reach.next(
    ~A,
    ~V,
    ~succ,
    List.append(&2, A, xs, ys),
    g
  )
    == List.append(
      &2,
      A,
      Reach.next(~A, ~V, ~succ, xs, g),
      Reach.next(~A, ~V, ~succ, ys, g)
    ): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      next1 = Reach.next(~A, ~V, ~succ, r, g)
      next2 = Reach.next(~A, ~V, ~succ, ys, g)
      %Equal.sym(
        List<&2, A>,
        Reach.next(~A, ~V, ~succ, List.append(&2, A, r, ys), g),
        List.append(&2, A, next1, next2),
        Reach.next_append(~A, ~V, ~succ, r, ys, g)
      ): {
        List.append(
          &2,
          A,
          succ(g)(x),
          _
        )
          == List.append(&2, A, List.append(&2, A, succ(g)(x), next1), next2): List<&2, A>
      }
      Equal.sym(
        List<&2, A>,
        List.append(&2, A, List.append(&2, A, succ(g)(x), next1), next2),
        List.append(&2, A, succ(g)(x), List.append(&2, A, next1, next2)),
        Shared.List.append_assoc(A, succ(g)(x), next1, next2)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.succ_within at the first node z of zs, by whether it is x (hit)
def Reach.succ_within.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +hit: Bool,
  z: A,
  r: List<&2, A>,
  +x: A,
  +g: V,
  ih: {
    List.contains(~A, ~same, r, x) == True{}: Bool
  } -> {Shared.List.within(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, r, g)) == True{}: Bool}
) -> {
  same(z, x) == hit: Bool
} -> {
  List.any.if(u => List.contains(~A, ~same, r, x), hit) == True{}: Bool
} -> {
  Shared.List.within(
    ~A,
    ~same,
    succ(g)(x),
    List.append(&2, A, succ(g)(z), Reach.next(~A, ~V, ~succ, r, g))
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => +h =>
        %Equal.sym(
          A,
          z,
          x,
          Shared.Eq.sound(~A, ~same, laws, z)(x)(he)
        ): {
          Shared.List.within(
            ~A,
            ~same,
            succ(g)(x),
            List.append(&2, A, succ(g)(_), Reach.next(~A, ~V, ~succ, r, g))
          )
            == True{}: Bool
        }
        Reach.within_left(
          ~A,
          ~same,
          succ(g)(x),
          succ(g)(x),
          Reach.next(~A, ~V, ~succ, r, g)
        )(Reach.within_self(~A, ~same, ~laws, succ(g)(x)))
    case False{}:
      +he => +h => Reach.within_right(
        ~A,
        ~same,
        succ(g)(x),
        succ(g)(z),
        Reach.next(~A, ~V, ~succ, r, g)
      )(ih(h))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the successors of a node x of zs are within the next level
def Reach.succ_within(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +zs: List<&2, A>,
  +x: A,
  +g: V
) -> {
  List.contains(~A, ~same, zs, x) == True{}: Bool
} -> {Shared.List.within(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, zs, g)) == True{}: Bool}:
  match zs:
    case Nil{}:
      +h => Empty.absurd(
        {Shared.List.within(~A, ~same, succ(g)(x), Reach.next(~A, ~V, ~succ, [], g)) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+z, +r}:
      Reach.succ_within.at(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        same(z, x),
        z,
        r,
        x,
        g,
        Reach.succ_within(~A, ~V, ~same, ~succ, ~laws, r, x, g)
      )({==})

# bend-lint: expect-begin bend-lint-rules/performance/loop_invariant_call@information -- a proof: it does not run
# the next level of xs is within the next level of zs, when xs is within zs
def Reach.next_within(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +zs: List<&2, A>,
  +g: V
) -> {
  Shared.List.within(~A, ~same, xs, zs) == True{}: Bool
} -> {
  Shared.List.within(
    ~A,
    ~same,
    Reach.next(~A, ~V, ~succ, xs, g),
    Reach.next(~A, ~V, ~succ, zs, g)
  )
    == True{}: Bool
}:
  match xs:
    case Nil{}:
      +h => {==}
    case Con{+x, +r}:
      +h =>
        +contains1 = List.contains(~A, ~same, zs, x)
        +within1 = Shared.List.within(~A, ~same, r, zs)
        Reach.within_both(
          ~A,
          ~same,
          succ(g)(x),
          Reach.next(~A, ~V, ~succ, r, g),
          Reach.next(~A, ~V, ~succ, zs, g)
        )(
          Reach.succ_within(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            zs,
            x,
            g
          )(Shared.Bool.and_true_left(contains1, within1)(h))
        )(
          Reach.next_within(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            r,
            zs,
            g
          )(Shared.Bool.and_true_right(contains1, within1)(h))
        )
# bend-lint: expect-end bend-lint-rules/performance/loop_invariant_call@information

# Reach.or_within once each side is known: a or y is a or z, when y gives z
# and z gives a or y
def Reach.or_within.at(
  a: Bool,
  y: Bool,
  z: Bool
) -> (
  {y == True{}: Bool} -> {z == True{}: Bool}
) -> (
  {z == True{}: Bool} -> {Bool.or(a, y) == True{}: Bool}
) -> {Bool.or(a, y) == Bool.or(a, z): Bool}:
  match a y z:
    case True{} y z:
      f => g => {==}
    case False{} True{} True{}:
      f => g => {==}
    case False{} True{} False{}:
      f => g => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(f({==})))
    case False{} False{} True{}:
      f => g => g({==})
    case False{} False{} False{}:
      f => g => {==}

# ks and then ys holds what ks or zs holds, when ys is within zs and zs is
# within ks and then ys
def Reach.or_within(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +ks: List<&2, A>,
  +ys: List<&2, A>,
  +zs: List<&2, A>,
  +m: A
) -> {
  Shared.List.within(~A, ~same, ys, zs) == True{}: Bool
} -> {
  Shared.List.within(~A, ~same, zs, List.append(&2, A, ks, ys)) == True{}: Bool
} -> {
  List.contains(
    ~A,
    ~same,
    List.append(&2, A, ks, ys),
    m
  )
    == Bool.or(List.contains(~A, ~same, ks, m), List.contains(~A, ~same, zs, m)): Bool
}:
  +h1 => +h2 =>
    +contains1 = List.contains(~A, ~same, ks, m)
    +contains2 = List.contains(~A, ~same, ys, m)
    +contains3 = List.contains(~A, ~same, List.append(&2, A, ks, ys), m)
    Equal.trans(
      Bool,
      contains3,
      Bool.or(contains1, contains2),
      Bool.or(contains1, List.contains(~A, ~same, zs, m)),
      Shared.List.contains_append(~A, ~same, ks, ys, m),
      Reach.or_within.at(
        contains1,
        contains2,
        List.contains(~A, ~same, zs, m)
      )(
        Reach.within_in(~A, ~same, ~laws, ys, zs, m)(h1)
      )(
        hz => Equal.trans(
          Bool,
          Bool.or(contains1, contains2),
          contains3,
          True{},
          Equal.sym(
            Bool,
            contains3,
            Bool.or(contains1, contains2),
            Shared.List.contains_append(~A, ~same, ks, ys, m)
          ),
          Reach.within_in(~A, ~same, ~laws, zs, List.append(&2, A, ks, ys), m)(h2)(hz)
        )
      )
    )

# the next level of ks and then ys is within ks, ys and the next level of ys,
# when the next level of ks is within ks and then ys
def Reach.next_grown(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ks: List<&2, A>,
  +ys: List<&2, A>,
  +g: V
) -> {
  Shared.List.within(
    ~A,
    ~same,
    Reach.next(~A, ~V, ~succ, ks, g),
    List.append(&2, A, ks, ys)
  )
    == True{}: Bool
} -> {
  Shared.List.within(
    ~A,
    ~same,
    Reach.next(~A, ~V, ~succ, List.append(&2, A, ks, ys), g),
    List.append(&2, A, List.append(&2, A, ks, ys), Reach.next(~A, ~V, ~succ, ys, g))
  )
    == True{}: Bool
}:
  +h =>
    +next1 = Reach.next(~A, ~V, ~succ, ks, g)
    +next2 = Reach.next(~A, ~V, ~succ, ys, g)
    +append1 = List.append(&2, A, ks, ys)
    %Equal.sym(
      List<&2, A>,
      Reach.next(~A, ~V, ~succ, append1, g),
      List.append(&2, A, next1, next2),
      Reach.next_append(~A, ~V, ~succ, ks, ys, g)
    ): {Shared.List.within(~A, ~same, _, List.append(&2, A, append1, next2)) == True{}: Bool}
    Reach.within_both(
      ~A,
      ~same,
      next1,
      next2,
      List.append(&2, A, append1, next2)
    )(
      Reach.within_left(~A, ~same, next1, append1, next2)(h)
    )(
      Reach.within_right(
        ~A,
        ~same,
        next2,
        append1,
        next2
      )(Reach.within_self(~A, ~same, ~laws, next2))
    )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.has_set, by whether y is a (hit)
def Reach.has_set.at(
  +hit: Bool,
  t: Crits.Dict(Unit),
  +y: List<&2, U32>,
  +a: List<&2, U32>
) -> {
  Crits.Key.is_eq(y, a) == hit: Bool
} -> {
  Crits.Dict.has(
    Unit,
    Crits.Dict.set(~Unit, t, y, Unit{}),
    a
  )
    == List.any.if(u => Crits.Dict.has(Unit, t, a), hit): Bool
}:
  match hit:
    case True{}:
      +he =>
        %Crits.Key.is_eq_sound(
          y,
          a
        )(he): {Crits.Dict.has(Unit, Crits.Dict.set(~Unit, t, y, Unit{}), _) == True{}: Bool}
        %Equal.sym(
          Maybe<&2, Unit>,
          Crits.Dict.get(Unit, Crits.Dict.set(~Unit, t, y, Unit{}), y),
          Bool.pick(
            Maybe<&2, Unit>,
            Crits.Key.is_eq(y, y),
            Some{Unit{}},
            Crits.Dict.get(Unit, t, y)
          ),
          Crits.Dict.get_set(~Unit, t, y, Unit{}, y)
        ): {Maybe.is_some(&2, Unit, _) == True{}: Bool}
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(y, y),
          True{},
          Crits.Key.is_eq_refl(y)
        ): {
          Maybe.is_some(
            &2,
            Unit,
            Bool.pick(Maybe<&2, Unit>, _, Some{Unit{}}, Crits.Dict.get(Unit, t, y))
          )
            == True{}: Bool
        }
        {==}
    case False{}:
      +he =>
        %Equal.sym(
          Maybe<&2, Unit>,
          Crits.Dict.get(Unit, Crits.Dict.set(~Unit, t, y, Unit{}), a),
          Bool.pick(
            Maybe<&2, Unit>,
            Crits.Key.is_eq(a, y),
            Some{Unit{}},
            Crits.Dict.get(Unit, t, a)
          ),
          Crits.Dict.get_set(~Unit, t, y, Unit{}, a)
        ): {Maybe.is_some(&2, Unit, _) == Crits.Dict.has(Unit, t, a): Bool}
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(a, y),
          False{},
          Shared.Eq.ne_flip(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            ~Crits.Key.laws(),
            y,
            a,
            he
          )
        ): {
          Maybe.is_some(
            &2,
            Unit,
            Bool.pick(Maybe<&2, Unit>, _, Some{Unit{}}, Crits.Dict.get(Unit, t, a))
          )
            == Crits.Dict.has(Unit, t, a): Bool
        }
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# t with the key y holds a exactly when y is a, or t holds a
def Reach.has_set(
  t: Crits.Dict(Unit),
  +y: List<&2, U32>,
  +a: List<&2, U32>
) -> {
  Crits.Dict.has(
    Unit,
    Crits.Dict.set(~Unit, t, y, Unit{}),
    a
  )
    == List.any.if(u => Crits.Dict.has(Unit, t, a), Crits.Key.is_eq(y, a)): Bool
}:
  Reach.has_set.at(Crits.Key.is_eq(y, a), t, y, a)({==})

# Reach.has_put at the first key, by whether it is a (s) and the rest holds a
# (c)
def Reach.has_put.at(
  s: Bool,
  c: Bool,
  h: Bool
) -> {Bool.or(c, List.any.if(u => h, s)) == Bool.or(List.any.if(u => c, s), h): Bool}:
  match s c:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} b:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# t with the keys ys holds a exactly when ys holds a, or t does
def Reach.has_put(
  +ys: List<&2, List<&2, U32>>,
  +t: Crits.Dict(Unit),
  +a: List<&2, U32>
) -> {
  Crits.Dict.has(
    Unit,
    Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ys, t),
    a
  )
    == Bool.or(
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ys, a),
      Crits.Dict.has(Unit, t, a)
    ): Bool
}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a)
      set1 = Crits.Dict.set(~Unit, t, y, Unit{})
      Equal.trans(
        Bool,
        Crits.Dict.has(Unit, Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, r, set1), a),
        Bool.or(contains1, Crits.Dict.has(Unit, set1, a)),
        Bool.or(List.any.if(u => contains1, Crits.Key.is_eq(y, a)), Crits.Dict.has(Unit, t, a)),
        Reach.has_put(r, set1, a),
        (
          %Equal.sym(Bool, Crits.Dict.has(Unit, set1, a), List.any.if(u => Crits.Dict.has(Unit, t, a), Crits.Key.is_eq(y, a)), Reach.has_set(t, y, a)): {Bool.or(contains1, _) == Bool.or(List.any.if(u => contains1, Crits.Key.is_eq(y, a)), Crits.Dict.has(Unit, t, a)): Bool}
          Reach.has_put.at(Crits.Key.is_eq(y, a), contains1, Crits.Dict.has(Unit, t, a)))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the trie of the keys ks holds a exactly when ks does
def Reach.has_keys(
  +ks: List<&2, List<&2, U32>>,
  +a: List<&2, U32>
) -> {
  Crits.Dict.has(
    Unit,
    Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit)),
    a
  )
    == List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a): Bool
}:
  Equal.trans(
    Bool,
    Crits.Dict.has(
      Unit,
      Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit)),
      a
    ),
    Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a), False{}),
    List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a),
    Reach.has_put(ks, Crits.Dict.new(~Unit), a),
    Equal.sym(
      Bool,
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a),
      Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a), False{}),
      Shared.Bool.or_false(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, a))
    )
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Reach.unique_in at the first node x, by whether t holds it (seen) and it is
# a (hit)
def Reach.unique_in.at(
  +seen: Bool,
  +hit: Bool,
  +x: List<&2, U32>,
  r: List<&2, List<&2, U32>>,
  +t: Crits.Dict(Unit),
  +a: List<&2, U32>,
  ih1: {
    List.contains(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
      a
    )
      == Bool.and(
        List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a),
        Bool.not(Crits.Dict.has(Unit, t, a))
      ): Bool
  },
  ih2: {
    List.contains(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, Crits.Dict.set(~Unit, t, x, Unit{})),
      a
    )
      == Bool.and(
        List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a),
        Bool.not(Crits.Dict.has(Unit, Crits.Dict.set(~Unit, t, x, Unit{}), a))
      ): Bool
  }
) -> {
  Crits.Dict.has(Unit, t, x) == seen: Bool
} -> {
  Crits.Key.is_eq(x, a) == hit: Bool
} -> {
  List.contains(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Shared.Bool.when(
      List<&2, List<&2, U32>>,
      seen,
      u => Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
      u => x
        <> Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, Crits.Dict.set(~Unit, t, x, Unit{}))
    ),
    a
  )
    == Bool.and(
      List.any.if(u => List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a), hit),
      Bool.not(Crits.Dict.has(Unit, t, a))
    ): Bool
}:
  match seen hit:
    case True{} True{}:
      +es => +eh =>
        +contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a)
        %Equal.sym(Bool, Crits.Dict.has(Unit, t, a), True{}, (
            %Crits.Key.is_eq_sound(x, a)(eh): {Crits.Dict.has(Unit, t, _) == True{}: Bool}
            es)): {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t), a) == Bool.not(_): Bool}
        Equal.trans(
          Bool,
          List.contains(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
            a
          ),
          Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, t, a))),
          False{},
          ih1,
          (
            %Equal.sym(Bool, Crits.Dict.has(Unit, t, a), True{}, (
              %Crits.Key.is_eq_sound(x, a)(eh): {Crits.Dict.has(Unit, t, _) == True{}: Bool}
              es)): {Bool.and(contains1, Bool.not(_)) == False{}: Bool}
            Shared.Bool.and_false_right(contains1))
        )
    case True{} False{}:
      +es => +eh => ih1
    case False{} True{}:
      +es => +eh =>
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(x, a),
          True{},
          eh
        ): {
          List.any.if(
            u => List.contains(
              ~List<&2, U32>,
              ~Crits.Key.is_eq,
              Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, Crits.Dict.set(~Unit, t, x, Unit{})),
              a
            ),
            _
          )
            == Bool.not(Crits.Dict.has(Unit, t, a)): Bool
        }
        %Equal.sym(Bool, Crits.Dict.has(Unit, t, a), False{}, (
            %Crits.Key.is_eq_sound(x, a)(eh): {Crits.Dict.has(Unit, t, _) == False{}: Bool}
            es)): {True{} == Bool.not(_): Bool}
        {==}
    case False{} False{}:
      +es => +eh =>
        +contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, a)
        +set1 = Crits.Dict.set(~Unit, t, x, Unit{})
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(x, a),
          False{},
          eh
        ): {
          List.any.if(
            u => List.contains(
              ~List<&2, U32>,
              ~Crits.Key.is_eq,
              Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, set1),
              a
            ),
            _
          )
            == Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, t, a))): Bool
        }
        Equal.trans(
          Bool,
          List.contains(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, set1),
            a
          ),
          Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, set1, a))),
          Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, t, a))),
          ih2,
          (
            %Equal.sym(Bool, Crits.Dict.has(Unit, set1, a), List.any.if(u => Crits.Dict.has(Unit, t, a), Crits.Key.is_eq(x, a)), Reach.has_set(t, x, a)): {Bool.and(contains1, Bool.not(_)) == Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, t, a))): Bool}
            %Equal.sym(Bool, Crits.Key.is_eq(x, a), False{}, eh): {Bool.and(contains1, Bool.not(List.any.if(u => Crits.Dict.has(Unit, t, a), _))) == Bool.and(contains1, Bool.not(Crits.Dict.has(Unit, t, a))): Bool}
            {==})
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
# a is one of the new nodes of xs exactly when it is in xs and t lacks it
def Reach.unique_in(
  +xs: List<&2, List<&2, U32>>,
  +t: Crits.Dict(Unit),
  +a: List<&2, U32>
) -> {
  List.contains(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Crits.Dict.unique(~List<&2, U32>, ~Reach.key, xs, t),
    a
  )
    == Bool.and(
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, xs, a),
      Bool.not(Crits.Dict.has(Unit, t, a))
    ): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Reach.unique_in.at(
        Crits.Dict.has(Unit, t, x),
        Crits.Key.is_eq(x, a),
        x,
        r,
        t,
        a,
        Reach.unique_in(r, t, a),
        Reach.unique_in(r, Crits.Dict.set(~Unit, t, x, Unit{}), a)
      )({==})({==})
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the keys of a and then b, put in t, are those of a put first, then of b
def Reach.put_append(
  +a: List<&2, List<&2, U32>>,
  b: List<&2, List<&2, U32>>,
  t: Crits.Dict(Unit)
) -> {
  Crits.Dict.put_keys(
    ~List<&2, U32>,
    ~Reach.key,
    List.append(&2, List<&2, U32>, a, b),
    t
  )
    == Crits.Dict.put_keys(
      ~List<&2, U32>,
      ~Reach.key,
      b,
      Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, a, t)
    ): Crits.Dict(Unit)
}:
  match a:
    case Nil{}:
      {==}
    case Con{x, r}:
      Reach.put_append(r, b, Crits.Dict.set(~Unit, t, x, Unit{}))

# Reach.unique_within at the first node x, by whether t holds it (seen)
def Reach.unique_within.at(
  +seen: Bool,
  +x: List<&2, U32>,
  +r: List<&2, List<&2, U32>>,
  t: Crits.Dict(Unit),
  ih1: {
    Shared.List.within(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
      r
    )
      == True{}: Bool
  },
  ih2: {
    Shared.List.within(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, Crits.Dict.set(~Unit, t, x, Unit{})),
      r
    )
      == True{}: Bool
  }
) -> {
  Shared.List.within(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Shared.Bool.when(
      List<&2, List<&2, U32>>,
      seen,
      u => Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
      u => x
        <> Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, Crits.Dict.set(~Unit, t, x, Unit{}))
    ),
    x <> r
  )
    == True{}: Bool
}:
  match seen:
    case True{}:
      Reach.within_right(
        ~List<&2, U32>,
        ~Crits.Key.is_eq,
        Crits.Dict.unique(~List<&2, U32>, ~Reach.key, r, t),
        [x],
        r
      )(ih1)
    case False{}:
      unique1 = Crits.Dict.unique(
        ~List<&2, U32>,
        ~Reach.key,
        r,
        Crits.Dict.set(~Unit, t, x, Unit{})
      )
      %Equal.sym(
        Bool,
        Crits.Key.is_eq(x, x),
        True{},
        Crits.Key.is_eq_refl(x)
      ): {
        Bool.and(
          List.any.if(u => List.contains(~List<&2, U32>, ~Crits.Key.is_eq, r, x), _),
          Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, unique1, x <> r)
        )
          == True{}: Bool
      }
      Reach.within_right(~List<&2, U32>, ~Crits.Key.is_eq, unique1, [x], r)(ih2)

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
# the new nodes of ws are within ws
def Reach.unique_within(
  +ws: List<&2, List<&2, U32>>,
  +t: Crits.Dict(Unit)
) -> {
  Shared.List.within(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Crits.Dict.unique(~List<&2, U32>, ~Reach.key, ws, t),
    ws
  )
    == True{}: Bool
}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Reach.unique_within.at(
        Crits.Dict.has(Unit, t, x),
        x,
        r,
        t,
        Reach.unique_within(r, t),
        Reach.unique_within(r, Crits.Dict.set(~Unit, t, x, Unit{}))
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# a node is seen, or it is new when it is not
def Reach.unique_has.at(seen: Bool) -> {Bool.or(seen, Bool.not(seen)) == True{}: Bool}:
  match seen:
    case True{}:
      {==}
    case False{}:
      {==}

# a node u of ws is one of the nodes seen, ks, or one of the new nodes
def Reach.unique_has(
  +ws: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>,
  +u: List<&2, U32>
) -> {
  List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ws, u) == True{}: Bool
} -> {
  List.contains(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    List.append(
      &2,
      List<&2, U32>,
      ks,
      Crits.Dict.unique(
        ~List<&2, U32>,
        ~Reach.key,
        ws,
        Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
      )
    ),
    u
  )
    == True{}: Bool
}:
  +h =>
    +seen1 = Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
    +unique1 = Crits.Dict.unique(~List<&2, U32>, ~Reach.key, ws, seen1)
    +contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, u)
    %Equal.sym(
      Bool,
      List.contains(
        ~List<&2, U32>,
        ~Crits.Key.is_eq,
        List.append(&2, List<&2, U32>, ks, unique1),
        u
      ),
      Bool.or(contains1, List.contains(~List<&2, U32>, ~Crits.Key.is_eq, unique1, u)),
      Shared.List.contains_append(~List<&2, U32>, ~Crits.Key.is_eq, ks, unique1, u)
    ): {_ == True{}: Bool}
    %Equal.sym(
      Bool,
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, unique1, u),
      Bool.and(
        List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ws, u),
        Bool.not(Crits.Dict.has(Unit, seen1, u))
      ),
      Reach.unique_in(ws, seen1, u)
    ): {Bool.or(contains1, _) == True{}: Bool}
    %Equal.sym(
      Bool,
      Crits.Dict.has(Unit, seen1, u),
      contains1,
      Reach.has_keys(ks, u)
    ): {
      Bool.or(
        contains1,
        Bool.and(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ws, u), Bool.not(_))
      )
        == True{}: Bool
    }
    %Equal.sym(
      Bool,
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ws, u),
      True{},
      h
    ): {Bool.or(contains1, Bool.and(_, Bool.not(contains1))) == True{}: Bool}
    Reach.unique_has.at(contains1)

# the nodes us of ws are within the nodes seen, ks, and then the new nodes
def Reach.unique_covers(
  +us: List<&2, List<&2, U32>>,
  +ws: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>
) -> {
  Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, us, ws) == True{}: Bool
} -> {
  Shared.List.within(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    us,
    List.append(
      &2,
      List<&2, U32>,
      ks,
      Crits.Dict.unique(
        ~List<&2, U32>,
        ~Reach.key,
        ws,
        Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
      )
    )
  )
    == True{}: Bool
}:
  match us:
    case Nil{}:
      +h => {==}
    case Con{+u, +r}:
      +h =>
        +contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ws, u)
        +within1 = Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, r, ws)
        +append1 = List.append(
          &2,
          List<&2, U32>,
          ks,
          Crits.Dict.unique(
            ~List<&2, U32>,
            ~Reach.key,
            ws,
            Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
          )
        )
        Shared.Bool.and_both(
          List.contains(~List<&2, U32>, ~Crits.Key.is_eq, append1, u),
          Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, r, append1)
        )(
          Reach.unique_has(ws, ks, u)(Shared.Bool.and_true_left(contains1, within1)(h))
        )(Reach.unique_covers(r, ws, ks)(Shared.Bool.and_true_right(contains1, within1)(h)))

# a search one level deeper is a search from the next level of the new nodes
def Reach.fill_step(
  ~V: Data,
  ~succ: V -> List<&2, U32> -> List<&2, List<&2, U32>>,
  e: Nat,
  ws: List<&2, List<&2, U32>>,
  g: V,
  seen: Crits.Dict(Unit)
) -> {
  Reach.fill(
    ~V,
    ~succ,
    1n+e,
    ws,
    g,
    seen
  )
    == Reach.fill(
      ~V,
      ~succ,
      e,
      Reach.next(
        ~List<&2, U32>,
        ~V,
        ~succ,
        Crits.Dict.unique(~List<&2, U32>, ~Reach.key, ws, seen),
        g
      ),
      g,
      Crits.Dict.put_keys(
        ~List<&2, U32>,
        ~Reach.key,
        Crits.Dict.unique(~List<&2, U32>, ~Reach.key, ws, seen),
        seen
      )
    ): Crits.Dict(Unit)
}:
  match e ws:
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}
    case d Con{w, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the fast search finds what the nodes seen, ks, hold, and what the search
# finds from zs: the level ws is within zs, and zs and the next level of ks
# are within ks and then ws
def Reach.fill_go(
  ~V: Data,
  ~succ: V -> List<&2, U32> -> List<&2, List<&2, U32>>,
  +f: Nat,
  +ws: List<&2, List<&2, U32>>,
  +zs: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>,
  +g: V,
  +m: List<&2, U32>
) -> {
  Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, ws, zs) == True{}: Bool
} -> {
  Shared.List.within(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    zs,
    List.append(&2, List<&2, U32>, ks, ws)
  )
    == True{}: Bool
} -> {
  Shared.List.within(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Reach.next(~List<&2, U32>, ~V, ~succ, ks, g),
    List.append(&2, List<&2, U32>, ks, ws)
  )
    == True{}: Bool
} -> {
  Crits.Dict.has(
    Unit,
    Reach.fill(
      ~V,
      ~succ,
      f,
      ws,
      g,
      Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
    ),
    m
  )
    == Bool.or(
      List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
      Reach.go(~List<&2, U32>, ~V, ~Crits.Key.is_eq, ~succ, f, zs, g, m)
    ): Bool
}:
  match f:
    case 0n:
      +h1 => +h2 => h3 =>
        %Reach.put_append(
          ks,
          ws,
          Crits.Dict.new(~Unit)
        ): {
          Crits.Dict.has(
            Unit,
            _,
            m
          )
            == Bool.or(
              List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
              List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m)
            ): Bool
        }
        Equal.trans(
          Bool,
          Crits.Dict.has(
            Unit,
            Crits.Dict.put_keys(
              ~List<&2, U32>,
              ~Reach.key,
              List.append(&2, List<&2, U32>, ks, ws),
              Crits.Dict.new(~Unit)
            ),
            m
          ),
          List.contains(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            List.append(&2, List<&2, U32>, ks, ws),
            m
          ),
          Bool.or(
            List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
            List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m)
          ),
          Reach.has_keys(List.append(&2, List<&2, U32>, ks, ws), m),
          Reach.or_within(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            ~Crits.Key.laws(),
            ks,
            ws,
            zs,
            m
          )(h1)(h2)
        )
    case 1n+e:
      +h1 => +h2 => h3 =>
        +seen1 = Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, ks, Crits.Dict.new(~Unit))
        +unique1 = Crits.Dict.unique(~List<&2, U32>, ~Reach.key, ws, seen1)
        +append1 = List.append(&2, List<&2, U32>, ks, unique1)
        +next1 = Reach.next(~List<&2, U32>, ~V, ~succ, unique1, g)
        +next2 = Reach.next(~List<&2, U32>, ~V, ~succ, zs, g)
        +go1 = Reach.go(~List<&2, U32>, ~V, ~Crits.Key.is_eq, ~succ, e, next2, g, m)
        +a = Reach.within_both(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          ks,
          ws,
          append1
        )(
          Reach.within_left(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            ks,
            ks,
            unique1
          )(
            Reach.within_self(
              ~List<&2, U32>,
              ~Crits.Key.is_eq,
              ~Crits.Key.laws(),
              ks
            )
          )
        )(
          Reach.unique_covers(
            ws,
            ws,
            ks
          )(
            Reach.within_self(
              ~List<&2, U32>,
              ~Crits.Key.is_eq,
              ~Crits.Key.laws(),
              ws
            )
          )
        )
        +yz = Reach.within_trans(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          ~Crits.Key.laws(),
          unique1,
          ws,
          zs
        )(Reach.unique_within(ws, seen1))(h1)
        +b = Reach.within_trans(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          ~Crits.Key.laws(),
          zs,
          List.append(&2, List<&2, U32>, ks, ws),
          append1
        )(h2)(a)
        +j3 = Reach.next_grown(
          ~List<&2, U32>,
          ~V,
          ~Crits.Key.is_eq,
          ~succ,
          ~Crits.Key.laws(),
          ks,
          unique1,
          g
        )(
          Reach.within_trans(
            ~List<&2, U32>,
            ~Crits.Key.is_eq,
            ~Crits.Key.laws(),
            Reach.next(~List<&2, U32>, ~V, ~succ, ks, g),
            List.append(&2, List<&2, U32>, ks, ws),
            append1
          )(h3)(a)
        )
        %Equal.sym(
          Crits.Dict(Unit),
          Reach.fill(~V, ~succ, 1n+e, ws, g, seen1),
          Reach.fill(
            ~V,
            ~succ,
            e,
            next1,
            g,
            Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, unique1, seen1)
          ),
          Reach.fill_step(~V, ~succ, e, ws, g, seen1)
        ): {
          Crits.Dict.has(
            Unit,
            _,
            m
          )
            == Bool.or(
              List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
              Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)
            ): Bool
        }
        %Reach.put_append(
          ks,
          unique1,
          Crits.Dict.new(~Unit)
        ): {
          Crits.Dict.has(
            Unit,
            Reach.fill(~V, ~succ, e, next1, g, _),
            m
          )
            == Bool.or(
              List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
              Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)
            ): Bool
        }
        Equal.trans(
          Bool,
          Crits.Dict.has(
            Unit,
            Reach.fill(
              ~V,
              ~succ,
              e,
              next1,
              g,
              Crits.Dict.put_keys(~List<&2, U32>, ~Reach.key, append1, Crits.Dict.new(~Unit))
            ),
            m
          ),
          Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, append1, m), go1),
          Bool.or(
            List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m),
            Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)
          ),
          Reach.fill_go(
            ~V,
            ~succ,
            e,
            next1,
            next2,
            append1,
            g,
            m
          )(
            Reach.next_within(
              ~List<&2, U32>,
              ~V,
              ~Crits.Key.is_eq,
              ~succ,
              ~Crits.Key.laws(),
              unique1,
              zs,
              g
            )(yz)
          )(
            Reach.within_trans(
              ~List<&2, U32>,
              ~Crits.Key.is_eq,
              ~Crits.Key.laws(),
              next2,
              Reach.next(~List<&2, U32>, ~V, ~succ, append1, g),
              List.append(&2, List<&2, U32>, append1, next1)
            )(
              Reach.next_within(
                ~List<&2, U32>,
                ~V,
                ~Crits.Key.is_eq,
                ~succ,
                ~Crits.Key.laws(),
                zs,
                append1,
                g
              )(b)
            )(j3)
          )(j3),
          (
            %Equal.sym(Bool, List.contains(~List<&2, U32>, ~Crits.Key.is_eq, append1, m), Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m), List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m)), Reach.or_within(~List<&2, U32>, ~Crits.Key.is_eq, ~Crits.Key.laws(), ks, unique1, zs, m)(yz)(b)): {Bool.or(_, go1) == Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m), Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)): Bool}
            Equal.sym(Bool, Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m), Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)), Bool.or(Bool.or(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m), List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m)), go1), Shared.Bool.or_assoc(List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ks, m), List.contains(~List<&2, U32>, ~Crits.Key.is_eq, zs, m), go1)))
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the fast search finds exactly what the search finds
law Reach.all_in:
  for ~V: Data
  for ~succ: V -> List<&2, U32> -> List<&2, List<&2, U32>>
  for ~nodes: V -> List<&2, List<&2, U32>>
  for +g: V
  for +x: List<&2, U32>
  for +m: List<&2, U32>
  {
    Crits.Dict.has(
      Unit,
      Reach.all(~V, ~succ, ~nodes, g, x),
      m
    )
      == Reach.in(~List<&2, U32>, ~V, ~Crits.Key.is_eq, ~succ, ~nodes, g, x, m): Bool
  }

def Reach.all_in(gt, succ, nodes, g, x, m):
  +level1 = succ(g)(x)
  Reach.fill_go(
    ~gt,
    ~succ,
    List.length(&2, List<&2, U32>, nodes(g)),
    level1,
    level1,
    [],
    g,
    m
  )(
    Reach.within_self(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      ~Crits.Key.laws(),
      level1
    )
  )(
    Reach.within_self(
      ~List<&2, U32>,
      ~Crits.Key.is_eq,
      ~Crits.Key.laws(),
      level1
    )
  )({==})

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Graphs by key
# -------------
# A graph whose nodes are trie keys: the successors of each node that has
# some, and those nodes. A search of it is the fast one (Reach.all).

# a graph: the successors of each node, and the nodes that have some
type Graph is Data:
  Graph{edges: Crits.Dict(List<&2, List<&2, U32>>), nodes: List<&2, List<&2, U32>>}

# a graph with no node
def Graph.new() -> Graph:
  Graph{Crits.Dict.new(~List<&2, List<&2, U32>>), []}

# the successors of the node k in g
def Graph.succ(g: Graph, k: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match g:
    case Graph{e, ns}:
      Maybe.default(
        &2,
        List<&2, List<&2, U32>>,
        Crits.Dict.get(List<&2, List<&2, U32>>, e, k),
        []
      )

# the nodes of g that have successors
def Graph.nodes(g: Graph) -> List<&2, List<&2, U32>>:
  match g:
    case Graph{e, ns}:
      ns

# Graph.link once the successors m of the node k are known
def Graph.link.at(
  e: Crits.Dict(List<&2, List<&2, U32>>),
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  t: List<&2, U32>,
  m: Maybe<&2, List<&2, List<&2, U32>>>
) -> Graph:
  match m:
    case None{}:
      Graph{Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, [t]), k <> ns}
    case Some{ts}:
      Graph{Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, t <> ts), ns}

# g with the node t as one more successor of the node k
def Graph.link(g: Graph, +k: List<&2, U32>, t: List<&2, U32>) -> Graph:
  match g:
    case Graph{+e, ns}:
      Graph.link.at(e, ns, k, t, Crits.Dict.get(List<&2, List<&2, U32>>, e, k))

# g with each node of ts as one more successor of the node k
def Graph.links(ts: List<&2, List<&2, U32>>, +k: List<&2, U32>, g: Graph) -> Graph:
  match ts:
    case Nil{}:
      g
    case Con{t, r}:
      Graph.links(r, k, Graph.link(g, k, t))

# g with the node t as one more successor of each node of ks
def Graph.back(ks: List<&2, List<&2, U32>>, +t: List<&2, U32>, g: Graph) -> Graph:
  match ks:
    case Nil{}:
      g
    case Con{k, r}:
      Graph.back(r, t, Graph.link(g, k, t))

# every node that a search of g finds from the node x, at any depth
def Graph.reach(g: Graph, x: List<&2, U32>) -> Crits.Dict(Unit):
  Reach.all(~Graph, ~Graph.succ, ~Graph.nodes, g, x)
