import Base
import ../../../../shared.bend as Shared

# Codes
# -----
# A code writes a value as tokens (U32s) in front of the tokens that follow
# it, and reads it back: reading what it wrote gives the value and what
# follows (Code.Laws). A list or a text carries its length first, in unary, so
# a read ends. Nodes send and store values as their codes, and two values are
# equal exactly when their codes are (Code.eq_laws).

# a value that a read gave, and the tokens after it
type Read<-A: Data> is Data:
  Read{value: A, rest: List<&2, U32>}

# reading what enc writes in front of any tokens gives the value and those
# tokens
def Code.Laws(
  -A: Data,
  enc: A -> List<&2, U32> -> List<&2, U32>,
  dec: List<&2, U32> -> Maybe<&2, Read<A>>
) -> Type:
  @a: A -> @r: List<&2, U32> -> {dec(enc(a)(r)) == Some{Read{a, r}}: Maybe<&2, Read<A>>}

# the read m, then k on its value and rest
def Read.then(
  -A: Data,
  -B: Data,
  m: Maybe<&2, Read<A>>,
  k: A -> List<&2, U32> -> Maybe<&2, Read<B>>
) -> Maybe<&2, Read<B>>:
  match m:
    case None{}:
      None{}
    case Some{Read{a, r}}:
      k(a)(r)

# a read that gave a, then k
def Read.then_some(
  -A: Data,
  -B: Data,
  m: Maybe<&2, Read<A>>,
  k: A -> List<&2, U32> -> Maybe<&2, Read<B>>,
  -a: A,
  -r: List<&2, U32>
) -> {
  m == Some{Read{a, r}}: Maybe<&2, Read<A>>
} -> {Read.then(A, B, m, k) == k(a)(r): Maybe<&2, Read<B>>}:
  h =>
    %Equal.sym(
      Maybe<&2, Read<A>>,
      m,
      Some{Read{a, r}},
      h
    ): {Read.then(A, B, _, k) == k(a)(r): Maybe<&2, Read<B>>}
    {==}

# Basic codes
# -----------

# the bit b, then r
def Code.bool(b: Bool, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case False{}:
      0 <> r
    case True{}:
      1 <> r

# a bit
def Code.bool.read(ts: List<&2, U32>) -> Maybe<&2, Read<Bool>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Some{Read{Bool.not(U32.is_eq(x, 0)), r}}

# the count n, in unary, then r
def Code.count(n: Nat, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      0 <> r
    case 1n+p:
      1 <> Code.count(p, r)

# a count
def Code.count.read(ts: List<&2, U32>) -> Maybe<&2, Read<Nat>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Read<Nat>>,
        U32.is_eq(x, 0),
        u => Some{Read{0n, r}},
        u => Read.then(Nat, Nat, Code.count.read(r), n => r2 => Some{Read{1n+n, r2}})
      )

# the characters of t, then r
def Code.chars(t: String, r: List<&2, U32>) -> List<&2, U32>:
  match t:
    case SNil{}:
      r
    case SCon{Chr{x}, rest}:
      x <> Code.chars(rest, r)

# the length of t
def Code.length(t: String) -> Nat:
  match t:
    case SNil{}:
      0n
    case SCon{c, rest}:
      1n+Code.length(rest)

# the text t, then r
def Code.text(t: String, r: List<&2, U32>) -> List<&2, U32>:
  +t = t
  Code.count(Code.length(t), Code.chars(t, r))

# n characters
def Code.chars.read(n: Nat, ts: List<&2, U32>) -> Maybe<&2, Read<String>>:
  match n ts:
    case 0n w:
      Some{Read{"", w}}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{x, r}:
      Read.then(String, String, Code.chars.read(p, r), t => r2 => Some{Read{SCon{Chr{x}, t}, r2}})

# a text
def Code.text.read(ts: List<&2, U32>) -> Maybe<&2, Read<String>>:
  Read.then(Nat, String, Code.count.read(ts), n => r => Code.chars.read(n, r))

# the value m, if any, then r
def Code.maybe(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  m: Maybe<&2, A>,
  r: List<&2, U32>
) -> List<&2, U32>:
  match m:
    case None{}:
      0 <> r
    case Some{a}:
      1 <> enc(a)(r)

# a value, if any
def Code.maybe.read(
  ~A: Data,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ts: List<&2, U32>
) -> Maybe<&2, Read<Maybe<&2, A>>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Read<Maybe<&2, A>>>,
        U32.is_eq(x, 0),
        u => Some{Read{None{}, r}},
        u => Read.then(A, Maybe<&2, A>, dec(r), a => r2 => Some{Read{Some{a}, r2}})
      )

# the items xs, then r
def Code.items(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  xs: List<&2, A>,
  r: List<&2, U32>
) -> List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{x, rest}:
      enc(x)(Code.items(~A, ~enc, rest, r))

# n items
def Code.items.read(
  ~A: Data,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  n: Nat,
  ts: List<&2, U32>
) -> Maybe<&2, Read<List<&2, A>>>:
  match n:
    case 0n:
      Some{Read{[], ts}}
    case 1n+p:
      Read.then(
        A,
        List<&2, A>,
        dec(ts),
        a => r => Read.then(
          List<&2, A>,
          List<&2, A>,
          Code.items.read(~A, ~dec, p, r),
          xs => r2 => Some{Read{a <> xs, r2}}
        )
      )

# the list xs, then r
def Code.list(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  +xs: List<&2, A>,
  r: List<&2, U32>
) -> List<&2, U32>:
  Code.count(List.length(&2, A, xs), Code.items(~A, ~enc, xs, r))

# a list
def Code.list.read(
  ~A: Data,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ts: List<&2, U32>
) -> Maybe<&2, Read<List<&2, A>>>:
  Read.then(Nat, List<&2, A>, Code.count.read(ts), n => r => Code.items.read(~A, ~dec, n, r))

# Laws
# ----

# a bit reads back
def Code.bool_read(
  b: Bool,
  r: List<&2, U32>
) -> {Code.bool.read(Code.bool(b, r)) == Some{Read{b, r}}: Maybe<&2, Read<Bool>>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a count reads back
def Code.count_read(
  n: Nat,
  r: List<&2, U32>
) -> {Code.count.read(Code.count(n, r)) == Some{Read{n, r}}: Maybe<&2, Read<Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      %Equal.sym(
        Maybe<&2, Read<Nat>>,
        Code.count.read(Code.count(np, r)),
        Some{Read{np, r}},
        Code.count_read(np, r)
      ):
        {
          Read.then(
            Nat,
            Nat,
            _,
            n => r2 => Some{Read{1n+n, r2}}
          )
            == Some{Read{1n+np, r}}: Maybe<&2, Read<Nat>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the characters of a text read back, given its length
def Code.chars_read(
  t: String,
  r: List<&2, U32>
) -> {
  Code.chars.read(Code.length(t), Code.chars(t, r)) == Some{Read{t, r}}: Maybe<&2, Read<String>>
}:
  match t:
    case SNil{}:
      {==}
    case SCon{head, tail}:
      match head:
        case Chr{code}:
          %Equal.sym(
            Maybe<&2, Read<String>>,
            Code.chars.read(Code.length(tail), Code.chars(tail, r)),
            Some{Read{tail, r}},
            Code.chars_read(tail, r)
          ):
            {
              Read.then(
                String,
                String,
                _,
                t => r2 => Some{Read{SCon{Chr{code}, t}, r2}}
              )
                == Some{Read{SCon{Chr{code}, tail}, r}}: Maybe<&2, Read<String>>
            }
          {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a text reads back
def Code.text_read(
  +t: String,
  r: List<&2, U32>
) -> {Code.text.read(Code.text(t, r)) == Some{Read{t, r}}: Maybe<&2, Read<String>>}:
  +r = r
  %Equal.sym(
    Maybe<&2, Read<Nat>>,
    Code.count.read(Code.count(Code.length(t), Code.chars(t, r))),
    Some{Read{Code.length(t), Code.chars(t, r)}},
    Code.count_read(Code.length(t), Code.chars(t, r))
  ):
    {
      Read.then(
        Nat,
        String,
        _,
        n => r => Code.chars.read(n, r)
      )
        == Some{Read{t, r}}: Maybe<&2, Read<String>>
    }
  Code.chars_read(t, r)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a value, if any, reads back, when its code does
def Code.maybe_read(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  laws: Code.Laws(A, enc, dec),
  m: Maybe<&2, A>,
  r: List<&2, U32>
) -> {
  Code.maybe.read(
    ~A,
    ~dec,
    Code.maybe(~A, ~enc, m, r)
  )
    == Some{Read{m, r}}: Maybe<&2, Read<Maybe<&2, A>>>
}:
  match m:
    case None{}:
      {==}
    case Some{value}:
      %Equal.sym(Maybe<&2, Read<A>>, dec(enc(value, r)), Some{Read{value, r}}, laws(value)(r)):
        {
          Read.then(
            A,
            Maybe<&2, A>,
            _,
            a => r2 => Some{Read{Some{a}, r2}}
          )
            == Some{Read{Some{value}, r}}: Maybe<&2, Read<Maybe<&2, A>>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# items read back, given their count, when their code does
def Code.items_read(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~laws: Code.Laws(A, enc, dec),
  +xs: List<&2, A>,
  +r: List<&2, U32>
) -> {
  Code.items.read(
    ~A,
    ~dec,
    List.length(&2, A, xs),
    Code.items(~A, ~enc, xs, r)
  )
    == Some{Read{xs, r}}: Maybe<&2, Read<List<&2, A>>>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      %Equal.sym(
        Maybe<&2, Read<A>>,
        dec(enc(x)(Code.items(~A, ~enc, rest, r))),
        Some{Read{x, Code.items(~A, ~enc, rest, r)}},
        laws(x)(Code.items(~A, ~enc, rest, r))
      ): {
        Read.then(
          A,
          List<&2, A>,
          _,
          a => r1 => Read.then(
            List<&2, A>,
            List<&2, A>,
            Code.items.read(~A, ~dec, List.length(&2, A, rest), r1),
            xs => r2 => Some{Read{a <> xs, r2}}
          )
        )
          == Some{Read{x <> rest, r}}: Maybe<&2, Read<List<&2, A>>>
      }
      %Equal.sym(
        Maybe<&2, Read<List<&2, A>>>,
        Code.items.read(~A, ~dec, List.length(&2, A, rest), Code.items(~A, ~enc, rest, r)),
        Some{Read{rest, r}},
        Code.items_read(~A, ~enc, ~dec, ~laws, rest, r)
      ): {
        Read.then(
          List<&2, A>,
          List<&2, A>,
          _,
          xs => r2 => Some{Read{x <> xs, r2}}
        )
          == Some{Read{x <> rest, r}}: Maybe<&2, Read<List<&2, A>>>
      }
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a list reads back, when the code of its items does
def Code.list_read(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~laws: Code.Laws(A, enc, dec),
  +xs: List<&2, A>,
  +r: List<&2, U32>
) -> {
  Code.list.read(
    ~A,
    ~dec,
    Code.list(~A, ~enc, xs, r)
  )
    == Some{Read{xs, r}}: Maybe<&2, Read<List<&2, A>>>
}:
  %Equal.sym(
    Maybe<&2, Read<Nat>>,
    Code.count.read(Code.count(List.length(&2, A, xs), Code.items(~A, ~enc, xs, r))),
    Some{Read{List.length(&2, A, xs), Code.items(~A, ~enc, xs, r)}},
    Code.count_read(List.length(&2, A, xs), Code.items(~A, ~enc, xs, r))
  ): {
    Read.then(
      Nat,
      List<&2, A>,
      _,
      n => r1 => Code.items.read(~A, ~dec, n, r1)
    )
      == Some{Read{xs, r}}: Maybe<&2, Read<List<&2, A>>>
  }
  Code.items_read(~A, ~enc, ~dec, ~laws, xs, r)

# a and b have the same code
def Code.is_eq(~A: Data, ~enc: A -> List<&2, U32> -> List<&2, U32>, a: A, b: A) -> Bool:
  Shared.List.is_eq(~U32, ~U32.is_eq, enc(a)([]), enc(b)([]))

# the code of a value, read back, is the value
def Code.read_value(-A: Data, m: Maybe<&2, Read<A>>, d: A) -> A:
  match m:
    case Some{Read{a, r}}:
      a
    case None{}:
      d

# two values with the same code are the same, when the code reads back
def Code.is_eq_sound(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~laws: Code.Laws(A, enc, dec),
  +a: A,
  +b: A
) -> {Code.is_eq(~A, ~enc, a, b) == True{}: Bool} -> {a == b: A}:
  h => Equal.trans(A, a, Code.read_value(A, dec(enc(b)([])), a), b, (
      %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), enc(a)([]), enc(b)([]))(h): {a == Code.read_value(A, dec(_), a): A}
      %Equal.sym(Maybe<&2, Read<A>>, dec(enc(a)([])), Some{Read{a, []}}, laws(a)([])): {a == Code.read_value(A, _, a): A}
      {==}), (
      %Equal.sym(Maybe<&2, Read<A>>, dec(enc(b)([])), Some{Read{b, []}}, laws(b)([])): {Code.read_value(A, _, a) == b: A}
      {==}))

# equality of codes is an equality, when the code reads back
def Code.eq_laws(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~laws: Code.Laws(A, enc, dec)
) -> Shared.Eq.Laws(A, Code.is_eq(~A, ~enc)):
  (
    a => Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), enc(a)([])),
    a => b => Code.is_eq_sound(~A, ~enc, ~dec, ~laws, a, b)
  )
