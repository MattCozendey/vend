import Base
import ./shared/keyset.bend as KeySets
import ./shared/shared/shared.bend as Shared
import ./shared/shared/trie.bend as Tries

# Machines
# --------
# A machine reads a word, one symbol of A at a time. g of V is what it knows,
# and x of S is its state: step(g)(x)(c) is the state after the symbol c, and
# ends(g)(x) says that the machine accepts a word that ends at x.

# the state after the word w, from x
def Machine.walk(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~step: V -> S -> A -> S,
  w: List<&2, A>,
  x: S,
  +g: V
) -> S:
  match w:
    case Nil{}:
      x
    case Con{c, t}:
      Machine.walk(~S, ~A, ~V, ~step, t, step(g)(x)(c), g)

# the machine accepts the word w from x
def Machine.accepts(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  w: List<&2, A>,
  x: S,
  +g: V
) -> Bool:
  ends(g)(Machine.walk(~S, ~A, ~V, ~step, w, x, g))

# Search
# ------
# A search visits the states that a machine can reach from a start state, the
# nearest first, each once. It moves the machine only under the symbols
# syms(g): the caller picks symbols that stand for all the others. A search
# needs no proof: its caller checks a word that it finds, and Cert.proves
# checks the states that it returns.

# A state to visit, with the symbols that lead to it, last first.
type Visit<-S: Data, -A: Data> is Data:
  Visit{x: S, rev: List<&2, A>}

# What a search found. Hit: a word that the machine accepts. Closed: every
# state that the machine can reach, when it accepts at none. Out: the search
# ran out of fuel.
type Found<-S: Data, -A: Data> is Data:
  Hit{word: List<&2, A>}
  Closed{states: List<&2, S>}
  Out{}

# The states to visit later (last first), and the states seen.
type Front<-S: Data, -A: Data> is Data:
  Front{back: List<&2, Visit<S, A>>, seen: Tries.Trie<S>}

# front, with y to visit after rev and d, unless known; k is the key of y
def Search.push.new(
  -S: Data,
  -A: Data,
  known: Bool,
  y: S,
  k: List<&2, Bool>,
  d: A,
  rev: List<&2, A>,
  front: Front<S, A>
) -> Front<S, A>:
  match known front:
    case True{} f:
      f
    case False{} Front{back, seen}:
      +y = y
      Front{Visit{y, d <> rev} <> back, Tries.Trie.set(S, seen, k, y)}

# front, with each state not seen that x steps to under a symbol of ds; the
# key of each state is made once, for both the lookup and the put
def Search.push(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ds: List<&2, A>,
  +x: S,
  +rev: List<&2, A>,
  front: Front<S, A>,
  +g: V
) -> Front<S, A>:
  match ds front:
    case Nil{} f:
      f
    case Con{+d, r} Front{back, +seen}:
      +y = step(g)(x)(d)
      +k = key(y)
      Search.push(
        ~S,
        ~A,
        ~V,
        ~same,
        ~key,
        ~step,
        r,
        x,
        rev,
        Search.push.new(
          S,
          A,
          KeySets.KeySet.has.at(~S, ~same, Tries.Trie.get(S, seen, k), y),
          y,
          k,
          d,
          rev,
          Front{back, seen}
        ),
        g
      )

# what a search finds from the states of todo, then those of back, in at most
# fuel steps
def Search.go(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  fuel: Nat,
  todo: List<&2, Visit<S, A>>,
  front: Front<S, A>,
  +g: V
) -> Found<S, A>:
  match fuel todo front:
    case 0n _ _:
      Out{}
    case 1n+n Nil{} Front{Nil{}, seen}:
      Closed{Tries.Trie.values(S, seen)}
    case 1n+n Nil{} Front{Con{b, r}, seen}:
      Search.go(
        ~S,
        ~A,
        ~V,
        ~same,
        ~key,
        ~step,
        ~ends,
        ~syms,
        n,
        List.reverse(&2, Visit<S, A>, b <> r),
        Front{[], seen},
        g
      )
    case 1n+n Con{Visit{+x, +rev}, t} f:
      Shared.Bool.when(
        Found<S, A>,
        ends(g)(x),
        u => Hit{List.reverse(&2, A, rev)},
        u => Search.go(
          ~S,
          ~A,
          ~V,
          ~same,
          ~key,
          ~step,
          ~ends,
          ~syms,
          n,
          t,
          Search.push(~S, ~A, ~V, ~same, ~key, ~step, syms(g), x, rev, f, g),
          g
        )
      )

# what a search finds from the state x, in at most fuel steps
def Search.run(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  fuel: Nat,
  +x: S,
  g: V
) -> Found<S, A>:
  Search.go(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~syms,
    fuel,
    [Visit{x, []}],
    Front{[], KeySets.KeySet.put(~S, ~key, Tries.Trie.new(S), x)},
    g
  )

# Certificates
# ------------
# A certificate is a list of states xs. When no state of xs ends a word, and
# each steps into xs under each symbol of syms(g), the machine accepts no word
# from a state of xs: given that covers(g)(x) holds of each, and that under a
# state that covers holds of, each symbol moves the machine as some symbol of
# syms(g) does (rep).

# x steps into t under each symbol of ds
def Cert.closed(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ds: List<&2, A>,
  +x: S,
  +t: Tries.Trie<S>,
  +g: V
) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      List.all.if(
        u => Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, r, x, t, g),
        KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(d))
      )

# x ends no word, covers holds of it, and it steps into t
def Cert.ok(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  +x: S,
  t: Tries.Trie<S>,
  +g: V
) -> Bool:
  List.all.if(
    u => List.all.if(
      u2 => Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, syms(g), x, t, g),
      covers(g)(x)
    ),
    Bool.not(ends(g)(x))
  )

# each state of ys is ok
def Cert.all_ok(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  ys: List<&2, S>,
  +t: Tries.Trie<S>,
  +g: V
) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, r}:
      List.all.if(
        u => Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, r, t, g),
        Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, y, t, g)
      )

# Cert.proves, with t the set of xs
def Cert.proves.at(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  xs: List<&2, S>,
  +t: Tries.Trie<S>,
  x: S,
  g: V
) -> Bool:
  List.all.if(
    u => Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, xs, t, g),
    KeySets.KeySet.has(~S, ~same, ~key, t, x)
  )

# xs is a certificate that holds x
def Cert.proves(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  +xs: List<&2, S>,
  x: S,
  g: V
) -> Bool:
  Cert.proves.at(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    xs,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    x,
    g
  )

# Cert.all_ok_in at the first state z of ys, by whether it is y (hit)
def Cert.all_ok_in.at(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(S, same),
  +hit: Bool,
  +z: S,
  r: List<&2, S>,
  y: S,
  +t: Tries.Trie<S>,
  +g: V,
  ih: {
    List.contains(~S, ~same, r, y) == True{}: Bool
  } -> {
    Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, r, t, g) == True{}: Bool
  } -> {Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, y, t, g) == True{}: Bool}
) -> {
  same(z, y) == hit: Bool
} -> {
  List.any.if(u => List.contains(~S, ~same, r, y), hit) == True{}: Bool
} -> {
  List.all.if(
    u => Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, r, t, g),
    Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, z, t, g)
  )
    == True{}: Bool
} -> {Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, y, t, g) == True{}: Bool}:
  match hit:
    case True{}:
      he => hc => ha =>
        %Shared.Eq.sound(
          ~S,
          ~same,
          laws,
          z
        )(
          y
        )(
          he
        ): {Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, _, t, g) == True{}: Bool}
        Shared.List.all.if_hit(
          Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, z, t, g),
          u => Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, r, t, g)
        )(ha)
    case False{}:
      he => hc => ha => ih(
        hc
      )(
        Shared.List.all.if_rest(
          Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, z, t, g),
          u => Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, r, t, g)
        )(ha)
      )

# a state y of ys is ok, when each state of ys is
def Cert.all_ok_in(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(S, same),
  ys: List<&2, S>,
  +y: S,
  +t: Tries.Trie<S>,
  +g: V
) -> {
  List.contains(~S, ~same, ys, y) == True{}: Bool
} -> {
  Cert.all_ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, ys, t, g) == True{}: Bool
} -> {Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, y, t, g) == True{}: Bool}:
  match ys:
    case Nil{}:
      hc => Empty.absurd(
        {
          True{} == True{}: Bool
        } -> {
          Cert.ok(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, y, t, g) == True{}: Bool
        },
        Shared.Bool.false_ne_true(hc)
      )
    case Con{+z, +r}:
      Cert.all_ok_in.at(
        ~S,
        ~A,
        ~V,
        ~same,
        ~key,
        ~step,
        ~ends,
        ~covers,
        ~syms,
        ~laws,
        same(z, y),
        z,
        r,
        y,
        t,
        g,
        Cert.all_ok_in(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, ~laws, r, y, t, g)
      )({==})

# Cert.closed_in at the first symbol e of ds, by whether it is d (hit)
def Cert.closed_in.at(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~asame: A -> A -> Bool,
  ~step: V -> S -> A -> S,
  ~alaws: Shared.Eq.Laws(A, asame),
  +hit: Bool,
  +e: A,
  r: List<&2, A>,
  d: A,
  +x: S,
  +t: Tries.Trie<S>,
  +g: V,
  ih: {
    List.contains(~A, ~asame, r, d) == True{}: Bool
  } -> {
    Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, r, x, t, g) == True{}: Bool
  } -> {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(d)) == True{}: Bool}
) -> {
  asame(e, d) == hit: Bool
} -> {
  List.any.if(u => List.contains(~A, ~asame, r, d), hit) == True{}: Bool
} -> {
  List.all.if(
    u => Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, r, x, t, g),
    KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(e))
  )
    == True{}: Bool
} -> {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(d)) == True{}: Bool}:
  match hit:
    case True{}:
      he => hc => ha =>
        %Shared.Eq.sound(
          ~A,
          ~asame,
          alaws,
          e
        )(d)(he): {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(_)) == True{}: Bool}
        Shared.List.all.if_hit(
          KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(e)),
          u => Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, r, x, t, g)
        )(ha)
    case False{}:
      he => hc => ha => ih(
        hc
      )(
        Shared.List.all.if_rest(
          KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(e)),
          u => Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, r, x, t, g)
        )(ha)
      )

# x steps into t under a symbol d of ds, when it does under each
def Cert.closed_in(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~asame: A -> A -> Bool,
  ~step: V -> S -> A -> S,
  ~alaws: Shared.Eq.Laws(A, asame),
  ds: List<&2, A>,
  +d: A,
  +x: S,
  +t: Tries.Trie<S>,
  +g: V
) -> {
  List.contains(~A, ~asame, ds, d) == True{}: Bool
} -> {
  Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, ds, x, t, g) == True{}: Bool
} -> {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(d)) == True{}: Bool}:
  match ds:
    case Nil{}:
      hc => Empty.absurd(
        {
          True{} == True{}: Bool
        } -> {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(d)) == True{}: Bool},
        Shared.Bool.false_ne_true(hc)
      )
    case Con{+e, +r}:
      Cert.closed_in.at(
        ~S,
        ~A,
        ~V,
        ~same,
        ~key,
        ~asame,
        ~step,
        ~alaws,
        asame(e, d),
        e,
        r,
        d,
        x,
        t,
        g,
        Cert.closed_in(~S, ~A, ~V, ~same, ~key, ~asame, ~step, ~alaws, r, d, x, t, g)
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# x steps into t under c, as it does under the symbol of syms(g) that p gives
def Cert.moved(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~asame: A -> A -> Bool,
  ~step: V -> S -> A -> S,
  ~syms: V -> List<&2, A>,
  ~alaws: Shared.Eq.Laws(A, asame),
  x: S,
  c: A,
  t: Tries.Trie<S>,
  +g: V,
  p: &d: A -> {
    List.contains(~A, ~asame, syms(g), d) == True{}: Bool
  }
    & {step(g)(x)(c) == step(g)(x)(d): S}
) -> {
  Cert.closed(~S, ~A, ~V, ~same, ~key, ~step, syms(g), x, t, g) == True{}: Bool
} -> {KeySets.KeySet.has(~S, ~same, ~key, t, step(g)(x)(c)) == True{}: Bool}:
  match p:
    case Tuple{d, Tuple{hin, heq}}:
      hcl =>
        %Equal.sym(
          S,
          step(g)(x)(c),
          step(g)(x)(d),
          heq
        ): {KeySets.KeySet.has(~S, ~same, ~key, t, _) == True{}: Bool}
        Cert.closed_in(
          ~S,
          ~A,
          ~V,
          ~same,
          ~key,
          ~asame,
          ~step,
          ~alaws,
          syms(g),
          d,
          x,
          t,
          g
        )(hin)(hcl)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a state y of the set of xs is ok, when each state of xs is
def Cert.held_ok(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(S, same),
  +xs: List<&2, S>,
  +y: S,
  g: V
) -> {
  Cert.all_ok(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    xs,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    g
  )
    == True{}: Bool
} -> {
  KeySets.KeySet.has(
    ~S,
    ~same,
    ~key,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    y
  )
    == True{}: Bool
} -> {
  Cert.ok(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    y,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    g
  )
    == True{}: Bool
}:
  ha => hh => Cert.all_ok_in(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    ~laws,
    xs,
    y,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    g
  )(KeySets.KeySet.has_put_all(~S, ~same, ~key, xs, y)(hh))(ha)

# the machine accepts no word from a state y of the set of xs, when xs is all ok
def Cert.sound.go(
  ~S: Data,
  ~A: Data,
  ~V: Data,
  ~same: S -> S -> Bool,
  ~key: S -> List<&2, Bool>,
  ~asame: A -> A -> Bool,
  ~step: V -> S -> A -> S,
  ~ends: V -> S -> Bool,
  ~covers: V -> S -> Bool,
  ~syms: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(S, same),
  ~alaws: Shared.Eq.Laws(A, asame),
  ~rep: @g: V -> @x: S -> @c: A -> {
    covers(g)(x) == True{}: Bool
  } -> (
    &d: A -> {
      List.contains(~A, ~asame, syms(g), d) == True{}: Bool
    }
      & {step(g)(x)(c) == step(g)(x)(d): S}
  ),
  w: List<&2, A>,
  +xs: List<&2, S>,
  +y: S,
  +g: V
) -> {
  Cert.all_ok(
    ~S,
    ~A,
    ~V,
    ~same,
    ~key,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    xs,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    g
  )
    == True{}: Bool
} -> {
  KeySets.KeySet.has(
    ~S,
    ~same,
    ~key,
    KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
    y
  )
    == True{}: Bool
} -> {Machine.accepts(~S, ~A, ~V, ~step, ~ends, w, y, g) == False{}: Bool}:
  match w:
    case Nil{}:
      ha => hh => Shared.Bool.not_true(
        ends(g)(y)
      )(
        Shared.List.all.if_hit(
          Bool.not(ends(g)(y)),
          u => List.all.if(
            u2 => Cert.closed(
              ~S,
              ~A,
              ~V,
              ~same,
              ~key,
              ~step,
              syms(g),
              y,
              KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
              g
            ),
            covers(g)(y)
          )
        )(
          Cert.held_ok(
            ~S,
            ~A,
            ~V,
            ~same,
            ~key,
            ~step,
            ~ends,
            ~covers,
            ~syms,
            ~laws,
            xs,
            y,
            g
          )(ha)(hh)
        )
      )
    case Con{+c, r}:
      +ha => hh =>
        +part = Shared.List.all.if_rest(
          Bool.not(ends(g)(y)),
          u => List.all.if(
            u2 => Cert.closed(
              ~S,
              ~A,
              ~V,
              ~same,
              ~key,
              ~step,
              syms(g),
              y,
              KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
              g
            ),
            covers(g)(y)
          )
        )(
          Cert.held_ok(
            ~S,
            ~A,
            ~V,
            ~same,
            ~key,
            ~step,
            ~ends,
            ~covers,
            ~syms,
            ~laws,
            xs,
            y,
            g
          )(ha)(hh)
        )
        Cert.sound.go(
          ~S,
          ~A,
          ~V,
          ~same,
          ~key,
          ~asame,
          ~step,
          ~ends,
          ~covers,
          ~syms,
          ~laws,
          ~alaws,
          ~rep,
          r,
          xs,
          step(g)(y)(c),
          g
        )(
          ha
        )(
          Cert.moved(
            ~S,
            ~A,
            ~V,
            ~same,
            ~key,
            ~asame,
            ~step,
            ~syms,
            ~alaws,
            y,
            c,
            KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
            g,
            rep(
              g
            )(
              y
            )(
              c
            )(
              Shared.List.all.if_hit(
                covers(g)(y),
                u2 => Cert.closed(
                  ~S,
                  ~A,
                  ~V,
                  ~same,
                  ~key,
                  ~step,
                  syms(g),
                  y,
                  KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
                  g
                )
              )(part)
            )
          )(
            Shared.List.all.if_rest(
              covers(g)(y),
              u2 => Cert.closed(
                ~S,
                ~A,
                ~V,
                ~same,
                ~key,
                ~step,
                syms(g),
                y,
                KeySets.KeySet.put_all(~S, ~key, xs, Tries.Trie.new(S)),
                g
              )
            )(part)
          )
        )

# the machine accepts no word from a state that a certificate holds
law Cert.sound:
  for ~S: Data
  for ~A: Data
  for ~V: Data
  for ~same: S -> S -> Bool
  for ~key: S -> List<&2, Bool>
  for ~asame: A -> A -> Bool
  for ~step: V -> S -> A -> S
  for ~ends: V -> S -> Bool
  for ~covers: V -> S -> Bool
  for ~syms: V -> List<&2, A>
  for ~laws: Shared.Eq.Laws(S, same)
  for ~alaws: Shared.Eq.Laws(A, asame)
  for ~rep: @g: V -> @x: S -> @c: A -> {
    covers(g)(x) == True{}: Bool
  } -> (
    &d: A -> {
      List.contains(~A, ~asame, syms(g), d) == True{}: Bool
    }
      & {step(g)(x)(c) == step(g)(x)(d): S}
  )
  for +xs: List<&2, S>
  for +x: S
  for +g: V
  for w: List<&2, A>
  {
    Cert.proves(~S, ~A, ~V, ~same, ~key, ~step, ~ends, ~covers, ~syms, xs, x, g) == True{}: Bool
  } -> {Machine.accepts(~S, ~A, ~V, ~step, ~ends, w, x, g) == False{}: Bool}

def Cert.sound(
  sty,
  aty,
  vty,
  same,
  key,
  asame,
  step,
  ends,
  covers,
  syms,
  laws,
  alaws,
  rep,
  xs,
  x,
  g,
  w
):
  +h => Cert.sound.go(
    ~sty,
    ~aty,
    ~vty,
    ~same,
    ~key,
    ~asame,
    ~step,
    ~ends,
    ~covers,
    ~syms,
    ~laws,
    ~alaws,
    ~rep,
    w,
    xs,
    x,
    g
  )(
    Shared.List.all.if_rest(
      KeySets.KeySet.has(
        ~sty,
        ~same,
        ~key,
        KeySets.KeySet.put_all(~sty, ~key, xs, Tries.Trie.new(sty)),
        x
      ),
      u => Cert.all_ok(
        ~sty,
        ~aty,
        ~vty,
        ~same,
        ~key,
        ~step,
        ~ends,
        ~covers,
        ~syms,
        xs,
        KeySets.KeySet.put_all(~sty, ~key, xs, Tries.Trie.new(sty)),
        g
      )
    )(h)
  )(
    Shared.List.all.if_hit(
      KeySets.KeySet.has(
        ~sty,
        ~same,
        ~key,
        KeySets.KeySet.put_all(~sty, ~key, xs, Tries.Trie.new(sty)),
        x
      ),
      u => Cert.all_ok(
        ~sty,
        ~aty,
        ~vty,
        ~same,
        ~key,
        ~step,
        ~ends,
        ~covers,
        ~syms,
        xs,
        KeySets.KeySet.put_all(~sty, ~key, xs, Tries.Trie.new(sty)),
        g
      )
    )(h)
  )
