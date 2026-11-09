import Base
import ../../../shared.bend as Shared

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

# every node of ps is in ks
def Reach.within(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>, +ks: List<&2, A>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, r}:
      Bool.and(List.contains(~A, ~same, ks, p), Reach.within(~A, ~same, r, ks))

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
} -> {Reach.within(~A, ~same, ps, nodes(g)) == True{}: Bool}:
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
  Reach.within(~A, ~same, ps, ks) == True{}: Bool
} -> {
  List.contains(~A, ~same, ps, p) == False{}: Bool
} -> {Reach.within(~A, ~same, ps, Shared.List.remove(~A, ~same, ks, p)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hw => +hn => {==}
    case Con{+q, +r}:
      +hw => +hn =>
        +remove1 = Shared.List.remove(~A, ~same, ks, p)
        +contains1 = List.contains(~A, ~same, ks, q)
        +within1 = Reach.within(~A, ~same, r, ks)
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
        ): {Bool.and(_, Reach.within(~A, ~same, r, remove1)) == True{}: Bool}
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
  Reach.within(~A, ~same, ps, ks) == True{}: Bool
} -> {Reach.fits(A, ps, List.length(&2, A, ks)) == True{}: Bool}:
  match ps:
    case Nil{}:
      +hd => +hw => {==}
    case Con{+p, +r}:
      +hd => +hw =>
        +contains1 = List.contains(~A, ~same, r, p)
        +remove1 = Shared.List.remove(~A, ~same, ks, p)
        +contains2 = List.contains(~A, ~same, ks, p)
        +within1 = Reach.within(~A, ~same, r, ks)
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

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Same graphs
# -----------
# A search of the graph g, and of a graph to(g) whose nodes have the same
# successors, finds the same: a graph can keep what its successors compute.
