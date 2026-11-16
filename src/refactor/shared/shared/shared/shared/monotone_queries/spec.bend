import Base

# A monotone query reads a state that only grows (more records) and answers
# Unknown while the state does not settle the answer, Known once it does, or
# Contradicted, with the keys of the records that prove that someone trusted
# lied. On a grown state it knows at least what it knew: a known answer stays,
# or becomes Contradicted. A known answer can be exact, or a range that only
# narrows; the order on known answers says which.
type MonotoneAnswer<-A: Data> is Data:
  Unknown{}
  Known{value: A}
  Contradicted{proof: List<&2, List<&2, U32>>}

# the answer y knows at least what the answer x knows, where Below says when a
# value knows at least what another value knows: Unknown knows least, Contradicted
# knows most, and a value is below a value that Below allows
def MonotoneAnswer.Below(
  ~A: Data,
  ~Below: A -> A -> Type,
  x: MonotoneAnswer<A>,
  y: MonotoneAnswer<A>
) -> Type:
  match x y:
    case Unknown{} _:
      Unit
    case Known{a} Known{b}:
      Below(a, b)
    case _ Contradicted{q}:
      Unit
    case _ _:
      Empty

# a number that is at least low, and at most high when high is there
type NumberRange is Data:
  NumberRange{low: Nat, high: Maybe<&2, Nat>}

# the range y lies within the range x: its low is not lower, and its high is
# not higher
def NumberRange.Below(x: NumberRange, y: NumberRange) -> Type:
  match x y:
    case NumberRange{a, h} NumberRange{b, None{}}:
      {Nat.is_le(a, b) == True{}: Bool} & {h == None{}: Maybe<&2, Nat>}
    case NumberRange{a, None{}} NumberRange{b, Some{k}}:
      {Nat.is_le(a, b) == True{}: Bool}
    case NumberRange{a, Some{j}} NumberRange{b, Some{k}}:
      {Nat.is_le(a, b) == True{}: Bool} & {Nat.is_le(k, j) == True{}: Bool}

# the query q is monotone: on a state t that grows from a state s, it knows at least
# what it knew on s
def MonotoneQuery(
  ~S: Data,
  ~Grows: S -> S -> Type,
  ~A: Data,
  ~Below: A -> A -> Type,
  ~q: S -> MonotoneAnswer<A>
) -> Type:
  @s: S -> @t: S -> Grows(s, t) -> MonotoneAnswer.Below(~A, ~Below, q(s), q(t))

# the answer of q2 for the value of x, on the state s; Unknown and Contradicted stay
def MonotoneQuery.then.at(
  ~S: Data,
  ~A: Data,
  ~B: Data,
  ~q2: A -> S -> MonotoneAnswer<B>,
  x: MonotoneAnswer<A>,
  s: S
) -> MonotoneAnswer<B>:
  match x:
    case Unknown{}:
      Unknown{}
    case Known{a}:
      q2(a, s)
    case Contradicted{p}:
      Contradicted{p}

# on the state s, the query q1, then the query q2 for its value
def MonotoneQuery.then(
  ~S: Data,
  ~A: Data,
  ~B: Data,
  ~q1: S -> MonotoneAnswer<A>,
  ~q2: A -> S -> MonotoneAnswer<B>,
  +s: S
) -> MonotoneAnswer<B>:
  MonotoneQuery.then.at(~S, ~A, ~B, ~q2, q1(s), s)

# the records fs are new, one after another, from the state s
def IncrementalStateMatchesQuery.Fresh(
  ~S: Data,
  ~F: Data,
  ~add: S -> F -> S,
  ~has: S -> F -> Bool,
  fs: List<&2, F>,
  s: S
) -> Type:
  match fs:
    case Nil{}:
      Unit
    case Con{f, rest}:
      {
        has(s, f) == False{}: Bool
      }
        & IncrementalStateMatchesQuery.Fresh(~S, ~F, ~add, ~has, rest, add(s, f))

# the state s after adding the records fs, one after another
def IncrementalStateMatchesQuery.adds(
  ~S: Data,
  ~F: Data,
  ~add: S -> F -> S,
  fs: List<&2, F>,
  s: S
) -> S:
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      IncrementalStateMatchesQuery.adds(~S, ~F, ~add, rest, add(s, f))

# the hook state t after stepping through the records fs, one after another
def IncrementalStateMatchesQuery.steps(
  ~T: Data,
  ~F: Data,
  ~step: T -> F -> T,
  fs: List<&2, F>,
  t: T
) -> T:
  match fs:
    case Nil{}:
      t
    case Con{f, rest}:
      IncrementalStateMatchesQuery.steps(~T, ~F, ~step, rest, step(t, f))

# a hook's own state agrees with the query q: for every list of new records, in
# any order, the state stepped through them from init reads as q reads the
# state that holds them, added to empty
def IncrementalStateMatchesQuery(
  ~S: Data,
  ~F: Data,
  ~T: Data,
  ~K: Data,
  ~empty: S,
  ~add: S -> F -> S,
  ~has: S -> F -> Bool,
  ~init: T,
  ~step: T -> F -> T,
  ~read: T -> K,
  ~q: S -> K
) -> Type:
  @fs: List<&2, F>
    -> IncrementalStateMatchesQuery.Fresh(~S, ~F, ~add, ~has, fs, empty)
    -> {
      read(
        IncrementalStateMatchesQuery.steps(~T, ~F, ~step, fs, init)
      )
        == q(IncrementalStateMatchesQuery.adds(~S, ~F, ~add, fs, empty)): K
    }

# Means: if the query q1 is monotone, and the query q2 knows at least as much for
# a value that knows more and on a state that grows, then "q1, then q2 for its
# value" is monotone.
# For free: a monotone query of a pair of monotone queries (q1, then q2 that pairs
# its value with q1's); a monotone query of a monotone function of a monotone query's
# value; Unknown and Contradicted pass through, so a lie found by q1 reaches every
# query built on it.
# For the goal: a hook builds its queries from smaller monotone queries ("the
# group of slot 5", then "the votes of that group") and gets their finality for
# free, so a known answer can be cached for good.
# Example: "the owners of branch main" is monotone, and "slot 5 of main is decided
# by those owners" is monotone for each set of owners, so "slot 5 of main is
# decided" is monotone.
law MonotoneQuery.then_is_monotone:
  for ~S: Data
  for ~Grows: S -> S -> Type
  for ~A: Data
  for ~BelowA: A -> A -> Type
  for ~B: Data
  for ~BelowB: B -> B -> Type
  for ~q1: S -> MonotoneAnswer<A>
  for ~q2: A -> S -> MonotoneAnswer<B>
  MonotoneQuery(~S, ~Grows, ~A, ~BelowA, ~q1)
    -> (
      @a: A -> @b: A -> @s: S -> @t: S -> BelowA(
        a,
        b
      ) -> Grows(s, t) -> MonotoneAnswer.Below(~B, ~BelowB, q2(a, s), q2(b, t))
    )
    -> MonotoneQuery(~S, ~Grows, ~B, ~BelowB, ~(s => MonotoneQuery.then(~S, ~A, ~B, ~q1, ~q2, s)))
