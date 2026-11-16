import Base

# An answer of a final query: Unknown while the facts do not settle it, a value
# once they do, or Broken, with the keys of the facts that prove that someone
# trusted lied. A final query never changes a known value, except to Broken. A
# value can be exact, or a range that only narrows: the order on values says
# which.
type Answer<-A: Data> is Data:
  Unknown{}
  Value{value: A}
  Broken{proof: List<&2, List<&2, U32>>}

# the answer y knows at least what the answer x knows, where Below says when a
# value knows at least what another value knows: Unknown knows least, Broken
# knows most, and a value is below a value that Below allows
def Answer.Below(~A: Data, ~Below: A -> A -> Type, x: Answer<A>, y: Answer<A>) -> Type:
  match x y:
    case Unknown{} _:
      Unit
    case Value{a} Value{b}:
      Below(a, b)
    case _ Broken{q}:
      Unit
    case _ _:
      Empty

# a number that is at least low, and at most high when high is there
type Range is Data:
  Range{low: Nat, high: Maybe<&2, Nat>}

# the range y lies within the range x: its low is not lower, and its high is
# not higher
def Range.Below(x: Range, y: Range) -> Type:
  match x y:
    case Range{a, h} Range{b, None{}}:
      {Nat.is_le(a, b) == True{}: Bool} & {h == None{}: Maybe<&2, Nat>}
    case Range{a, None{}} Range{b, Some{k}}:
      {Nat.is_le(a, b) == True{}: Bool}
    case Range{a, Some{j}} Range{b, Some{k}}:
      {Nat.is_le(a, b) == True{}: Bool} & {Nat.is_le(k, j) == True{}: Bool}

# the query q is final: on a state t that grows from a state s, it knows at least
# what it knew on s
def FinalQuery(
  ~S: Data,
  ~Grows: S -> S -> Type,
  ~A: Data,
  ~Below: A -> A -> Type,
  ~q: S -> Answer<A>
) -> Type:
  @s: S -> @t: S -> Grows(s, t) -> Answer.Below(~A, ~Below, q(s), q(t))

# the answer of q2 for the value of x, on the state s; Unknown and Broken stay
def Query.then.at(
  ~S: Data,
  ~A: Data,
  ~B: Data,
  ~q2: A -> S -> Answer<B>,
  x: Answer<A>,
  s: S
) -> Answer<B>:
  match x:
    case Unknown{}:
      Unknown{}
    case Value{a}:
      q2(a, s)
    case Broken{p}:
      Broken{p}

# on the state s, the query q1, then the query q2 for its value
def Query.then(
  ~S: Data,
  ~A: Data,
  ~B: Data,
  ~q1: S -> Answer<A>,
  ~q2: A -> S -> Answer<B>,
  +s: S
) -> Answer<B>:
  Query.then.at(~S, ~A, ~B, ~q2, q1(s), s)

# the facts fs are new, one after another, from the state s
def HookStateAgrees.Fresh(
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
      {has(s, f) == False{}: Bool} & HookStateAgrees.Fresh(~S, ~F, ~add, ~has, rest, add(s, f))

# the state s after adding the facts fs, one after another
def HookStateAgrees.adds(~S: Data, ~F: Data, ~add: S -> F -> S, fs: List<&2, F>, s: S) -> S:
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      HookStateAgrees.adds(~S, ~F, ~add, rest, add(s, f))

# the hook state t after stepping through the facts fs, one after another
def HookStateAgrees.steps(~T: Data, ~F: Data, ~step: T -> F -> T, fs: List<&2, F>, t: T) -> T:
  match fs:
    case Nil{}:
      t
    case Con{f, rest}:
      HookStateAgrees.steps(~T, ~F, ~step, rest, step(t, f))

# a hook's own state agrees with the query q: for every list of new facts, in
# any order, the state stepped through them from init reads as q reads the
# state that holds them, added to empty
def HookStateAgrees(
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
    -> HookStateAgrees.Fresh(~S, ~F, ~add, ~has, fs, empty)
    -> {
      read(
        HookStateAgrees.steps(~T, ~F, ~step, fs, init)
      )
        == q(HookStateAgrees.adds(~S, ~F, ~add, fs, empty)): K
    }

# Means: if the query q1 is final, and the query q2 knows at least as much for
# a value that knows more and on a state that grows, then "q1, then q2 for its
# value" is final.
# For free: a final query of a pair of final queries (q1, then q2 that pairs
# its value with q1's); a final query of a monotone function of a final query's
# value; Unknown and Broken pass through, so a lie found by q1 reaches every
# query built on it.
# For the goal: a hook builds its queries from smaller final queries ("the
# group of slot 5", then "the votes of that group") and gets their finality for
# free, so a known answer can be cached for good.
# Example: "the owners of branch main" is final, and "slot 5 of main is decided
# by those owners" is final for each set of owners, so "slot 5 of main is
# decided" is final.
law Query.then_is_final:
  for ~S: Data
  for ~Grows: S -> S -> Type
  for ~A: Data
  for ~BelowA: A -> A -> Type
  for ~B: Data
  for ~BelowB: B -> B -> Type
  for ~q1: S -> Answer<A>
  for ~q2: A -> S -> Answer<B>
  FinalQuery(~S, ~Grows, ~A, ~BelowA, ~q1)
    -> (
      @a: A -> @b: A -> @s: S -> @t: S -> BelowA(
        a,
        b
      ) -> Grows(s, t) -> Answer.Below(~B, ~BelowB, q2(a, s), q2(b, t))
    )
    -> FinalQuery(~S, ~Grows, ~B, ~BelowB, ~(s => Query.then(~S, ~A, ~B, ~q1, ~q2, s)))
