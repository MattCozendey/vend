import Base
import ./shared.bend as Shared

# Codes
# -----
# A code writes a value as tokens (U32s) in front of the tokens that follow
# it, and reads it back: reading what it wrote gives the value and what
# follows (Code.Laws). A list or a text carries its length first, so a read
# ends. A value alone is read whole (Code.whole.read): the read keeps it only
# when its code is exactly the words read, so words name one value and a value
# has one code. Two values are equal exactly when their codes are
# (Code.eq_laws).

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

# the value of a read that is the whole of some words: nothing follows it
def Read.whole(-A: Data, m: Maybe<&2, Read<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Read{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# how a value written by enc is read, and that it reads back
def Codec.Read(-A: Data, enc: A -> List<&2, U32> -> List<&2, U32>) -> Type:
  Sigma<&1, &1, List<&2, U32> -> Maybe<&2, Read<A>>, dec => Code.Laws(A, enc, dec)>

# a code of A: how a value is written, how one is read, and that reading what
# was written gives it back
def Codec(-A: Data) -> Type:
  Sigma<&1, &1, A -> List<&2, U32> -> List<&2, U32>, enc => Codec.Read(A, enc)>

# how c writes a value
def Codec.enc(-A: Data, c: Codec(A)) -> A -> List<&2, U32> -> List<&2, U32>:
  match c:
    case Tuple{e, d}:
      e

# how c reads a value
def Codec.dec(-A: Data, c: Codec(A)) -> List<&2, U32> -> Maybe<&2, Read<A>>:
  match c:
    case Tuple{e, Tuple{d, l}}:
      d

# that c reads back what it writes
def Codec.laws(-A: Data, c: Codec(A)) -> Code.Laws(A, Codec.enc(A, c), Codec.dec(A, c)):
  match c:
    case Tuple{e, Tuple{d, l}}:
      l

# Basic codes
# -----------

# the token x, then r
def Code.token(x: U32, r: List<&2, U32>) -> List<&2, U32>:
  x <> r

# a token
def Code.token.read(ts: List<&2, U32>) -> Maybe<&2, Read<U32>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Some{Read{x, r}}

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
    case Con{0, r}:
      Some{Read{False{}, r}}
    case Con{1, r}:
      Some{Read{True{}, r}}
    case _:
      None{}

# the character c, then r
def Code.char(c: Char, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Chr{x}:
      x <> r

# a character
def Code.char.read(ts: List<&2, U32>) -> Maybe<&2, Read<Char>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Some{Read{Chr{x}, r}}

# the count c + n, then r, where the digit c is below the top token
# 4294967295: each top token stands for that many, and a digit below the top
# ends the count, so a count below the top is one token
def Code.count.go(+n: Nat, c: U32, +r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      c <> r
    case 1n+p:
      +d = U32.inc(c)
      Shared.Bool.when(
        List<&2, U32>,
        U32.is_eq(d, 4294967295),
        u => d <> Code.count.go(p, 0, r),
        u => Code.count.go(p, d, r)
      )

# the count n, then r
def Code.count(n: Nat, r: List<&2, U32>) -> List<&2, U32>:
  Code.count.go(n, 0, r)

# a count
def Code.count.read(ts: List<&2, U32>) -> Maybe<&2, Read<Nat>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Read<Nat>>,
        U32.is_eq(x, 4294967295),
        u => Read.then(
          Nat,
          Nat,
          Code.count.read(r),
          n => r2 => Some{Read{Nat.add(U32.to_nat(x), n), r2}}
        ),
        u => Some{Read{U32.to_nat(x), r}}
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
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Read<Maybe<&2, A>>>,
        U32.is_eq(x, 0),
        u => Some{Read{None{}, r}},
        u => Shared.Bool.when(
          Maybe<&2, Read<Maybe<&2, A>>>,
          U32.is_eq(x, 1),
          u => Read.then(A, Maybe<&2, A>, dec(r), a => r2 => Some{Read{Some{a}, r2}}),
          u => None{}
        )
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

# the words ws, then r
def Code.words(ws: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  Code.list(~U32, ~Code.token, ws, r)

# words
def Code.words.read(ts: List<&2, U32>) -> Maybe<&2, Read<List<&2, U32>>>:
  Code.list.read(~U32, ~Code.token.read, ts)

# Fields
# ------
# A value of a type T is the values of its fields, made into a T: it is read
# as the reads of its fields, one after the other.

# a value of A, made into a T by mk
def Code.one.read(
  ~A: Data,
  ~T: Data,
  ~da: List<&2, U32> -> Maybe<&2, Read<A>>,
  mk: A -> T,
  ts: List<&2, U32>
) -> Maybe<&2, Read<T>>:
  Read.then(A, T, da(ts), a => r => Some{Read{mk(a), r}})

# values of A and B, made into a T by mk
def Code.two.read(
  ~A: Data,
  ~B: Data,
  ~T: Data,
  ~da: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~db: List<&2, U32> -> Maybe<&2, Read<B>>,
  mk: A -> B -> T,
  ts: List<&2, U32>
) -> Maybe<&2, Read<T>>:
  Read.then(A, T, da(ts), a => r => Code.one.read(~B, ~T, ~db, mk(a), r))

# values of A, B and C, made into a T by mk
def Code.three.read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~T: Data,
  ~da: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~db: List<&2, U32> -> Maybe<&2, Read<B>>,
  ~dc: List<&2, U32> -> Maybe<&2, Read<C>>,
  mk: A -> B -> C -> T,
  ts: List<&2, U32>
) -> Maybe<&2, Read<T>>:
  Read.then(A, T, da(ts), a => r => Code.two.read(~B, ~C, ~T, ~db, ~dc, mk(a), r))

# values of A, B, C and D, made into a T by mk
def Code.four.read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~D: Data,
  ~T: Data,
  ~da: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~db: List<&2, U32> -> Maybe<&2, Read<B>>,
  ~dc: List<&2, U32> -> Maybe<&2, Read<C>>,
  ~dd: List<&2, U32> -> Maybe<&2, Read<D>>,
  mk: A -> B -> C -> D -> T,
  ts: List<&2, U32>
) -> Maybe<&2, Read<T>>:
  Read.then(A, T, da(ts), a => r => Code.three.read(~B, ~C, ~D, ~T, ~db, ~dc, ~dd, mk(a), r))

# values of A, B, C, D and E, made into a T by mk
def Code.five.read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~D: Data,
  ~E: Data,
  ~T: Data,
  ~da: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~db: List<&2, U32> -> Maybe<&2, Read<B>>,
  ~dc: List<&2, U32> -> Maybe<&2, Read<C>>,
  ~dd: List<&2, U32> -> Maybe<&2, Read<D>>,
  ~de: List<&2, U32> -> Maybe<&2, Read<E>>,
  mk: A -> B -> C -> D -> E -> T,
  ts: List<&2, U32>
) -> Maybe<&2, Read<T>>:
  Read.then(A, T, da(ts), a => r => Code.four.read(~B, ~C, ~D, ~E, ~T, ~db, ~dc, ~dd, ~de, mk(a), r))

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Code.count_read.go one digit on, once it is known whether c + 1 is the top
# (b); ih is the law for the rest p
def Code.count_read.next(
  p: Nat,
  +c: U32,
  r: List<&2, U32>,
  h: {U32.is_eq(c, 4294967295) == False{}: Bool},
  b: Bool,
  eb: {U32.is_eq(U32.inc(c), 4294967295) == b: Bool},
  ih: @d: U32 -> {U32.is_eq(d, 4294967295) == False{}: Bool} -> {
    Code.count.read(Code.count.go(p, d, r))
      == Some{Read{Nat.add(U32.to_nat(d), p), r}}: Maybe<&2, Read<Nat>>
  }
) -> {
  Code.count.read(
    Shared.Bool.when(
      List<&2, U32>,
      b,
      u => U32.inc(c) <> Code.count.go(p, 0, r),
      u => Code.count.go(p, U32.inc(c), r)
    )
  )
    == Some{Read{Nat.add(U32.to_nat(c), 1n+p), r}}: Maybe<&2, Read<Nat>>
}:
  match b:
    case True{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(c), 1n+p), 1n+Nat.add(U32.to_nat(c), p), Shared.Nat.add_succ(U32.to_nat(c), p)): {
        Code.count.read(U32.inc(c) <> Code.count.go(p, 0, r)) == Some{Read{_, r}}: Maybe<&2, Read<Nat>>
      }
      %Shared.U32.inc_to_nat(c)(h): {
        Code.count.read(U32.inc(c) <> Code.count.go(p, 0, r)) == Some{Read{Nat.add(_, p), r}}: Maybe<&2, Read<Nat>>
      }
      %Equal.sym(Bool, U32.is_eq(U32.inc(c), 4294967295), True{}, eb): {
        Shared.Bool.when(
          Maybe<&2, Read<Nat>>,
          _,
          u => Read.then(
            Nat,
            Nat,
            Code.count.read(Code.count.go(p, 0, r)),
            n => r2 => Some{Read{Nat.add(U32.to_nat(U32.inc(c)), n), r2}}
          ),
          u => Some{Read{U32.to_nat(U32.inc(c)), Code.count.go(p, 0, r)}}
        )
          == Some{Read{Nat.add(U32.to_nat(U32.inc(c)), p), r}}: Maybe<&2, Read<Nat>>
      }
      %Equal.sym(
        Maybe<&2, Read<Nat>>,
        Code.count.read(Code.count.go(p, 0, r)),
        Some{Read{p, r}},
        ih(0)({==})
      ): {
        Read.then(
          Nat,
          Nat,
          _,
          n => r2 => Some{Read{Nat.add(U32.to_nat(U32.inc(c)), n), r2}}
        )
          == Some{Read{Nat.add(U32.to_nat(U32.inc(c)), p), r}}: Maybe<&2, Read<Nat>>
      }
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(c), 1n+p), 1n+Nat.add(U32.to_nat(c), p), Shared.Nat.add_succ(U32.to_nat(c), p)): {
        Code.count.read(Code.count.go(p, U32.inc(c), r)) == Some{Read{_, r}}: Maybe<&2, Read<Nat>>
      }
      %Shared.U32.inc_to_nat(c)(h): {
        Code.count.read(Code.count.go(p, U32.inc(c), r)) == Some{Read{Nat.add(_, p), r}}: Maybe<&2, Read<Nat>>
      }
      ih(U32.inc(c))(eb)

# a count from the digit c, below the top, reads back as c and n
def Code.count_read.go(
  +n: Nat,
  +c: U32,
  +r: List<&2, U32>,
  h: {U32.is_eq(c, 4294967295) == False{}: Bool}
) -> {
  Code.count.read(Code.count.go(n, c, r))
    == Some{Read{Nat.add(U32.to_nat(c), n), r}}: Maybe<&2, Read<Nat>>
}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(U32.to_nat(c), 0n), U32.to_nat(c), Shared.Nat.add_zero(U32.to_nat(c))): {
        Code.count.read(c <> r) == Some{Read{_, r}}: Maybe<&2, Read<Nat>>
      }
      %Equal.sym(Bool, U32.is_eq(c, 4294967295), False{}, h): {
        Shared.Bool.when(
          Maybe<&2, Read<Nat>>,
          _,
          u => Read.then(
            Nat,
            Nat,
            Code.count.read(r),
            n => r2 => Some{Read{Nat.add(U32.to_nat(c), n), r2}}
          ),
          u => Some{Read{U32.to_nat(c), r}}
        )
          == Some{Read{U32.to_nat(c), r}}: Maybe<&2, Read<Nat>>
      }
      {==}
    case 1n+p:
      Code.count_read.next(
        p,
        c,
        r,
        h,
        U32.is_eq(U32.inc(c), 4294967295),
        {==},
        d => hd => Code.count_read.go(p, d, r, hd)
      )

# Code.count_append one digit on, once it is known whether c + 1 is the top (b)
def Code.count_append.next(
  +p: Nat,
  +c: U32,
  +r: List<&2, U32>,
  +x: List<&2, U32>,
  b: Bool,
  ih: @d: U32 -> {
    List.append(&2, U32, Code.count.go(p, d, r), x) == Code.count.go(p, d, List.append(&2, U32, r, x)): List<&2, U32>
  }
) -> {
  List.append(
    &2,
    U32,
    Shared.Bool.when(
      List<&2, U32>,
      b,
      u => U32.inc(c) <> Code.count.go(p, 0, r),
      u => Code.count.go(p, U32.inc(c), r)
    ),
    x
  )
    == Shared.Bool.when(
      List<&2, U32>,
      b,
      u => U32.inc(c) <> Code.count.go(p, 0, List.append(&2, U32, r, x)),
      u => Code.count.go(p, U32.inc(c), List.append(&2, U32, r, x))
    ): List<&2, U32>
}:
  match b:
    case True{}:
      %Equal.sym(
        List<&2, U32>,
        List.append(&2, U32, Code.count.go(p, 0, r), x),
        Code.count.go(p, 0, List.append(&2, U32, r, x)),
        ih(0)
      ): {U32.inc(c) <> _ == U32.inc(c) <> Code.count.go(p, 0, List.append(&2, U32, r, x)): List<&2, U32>}
      {==}
    case False{}:
      ih(U32.inc(c))

# words after a count are the count of those words, then the rest
def Code.count_append(
  +n: Nat,
  +c: U32,
  +r: List<&2, U32>,
  +x: List<&2, U32>
) -> {
  List.append(&2, U32, Code.count.go(n, c, r), x) == Code.count.go(n, c, List.append(&2, U32, r, x)): List<&2, U32>
}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Code.count_append.next(p, c, r, x, U32.is_eq(U32.inc(c), 4294967295), d => Code.count_append(p, d, r, x))

# a count reads back
def Code.count_read(
  n: Nat,
  r: List<&2, U32>
) -> {Code.count.read(Code.count(n, r)) == Some{Read{n, r}}: Maybe<&2, Read<Nat>>}:
  Code.count_read.go(n, 0, r, {==})
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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
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
      items1 = Code.items(~A, ~enc, rest, r)
      length1 = List.length(&2, A, rest)
      %Equal.sym(
        Maybe<&2, Read<A>>,
        dec(enc(x)(items1)),
        Some{Read{x, items1}},
        laws(x)(items1)
      ): {
        Read.then(
          A,
          List<&2, A>,
          _,
          a => r1 => Read.then(
            List<&2, A>,
            List<&2, A>,
            Code.items.read(~A, ~dec, length1, r1),
            xs => r2 => Some{Read{a <> xs, r2}}
          )
        )
          == Some{Read{x <> rest, r}}: Maybe<&2, Read<List<&2, A>>>
      }
      %Equal.sym(
        Maybe<&2, Read<List<&2, A>>>,
        Code.items.read(~A, ~dec, length1, items1),
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
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
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
  items1 = Code.items(~A, ~enc, xs, r)
  length1 = List.length(&2, A, xs)
  %Equal.sym(
    Maybe<&2, Read<Nat>>,
    Code.count.read(Code.count(length1, items1)),
    Some{Read{length1, items1}},
    Code.count_read(length1, items1)
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
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a read m that gives a and r, then k, is k on a and r
def Read.then_some(
  -A: Data,
  -B: Data,
  -m: Maybe<&2, Read<A>>,
  -k: A -> List<&2, U32> -> Maybe<&2, Read<B>>,
  -a: A,
  -r: List<&2, U32>,
  e: {m == Some{Read{a, r}}: Maybe<&2, Read<A>>}
) -> {k(a)(r) == Read.then(A, B, m, k): Maybe<&2, Read<B>>}:
  %Equal.sym(
    Maybe<&2, Read<A>>,
    m,
    Some{Read{a, r}},
    e
  ): {k(a)(r) == Read.then(A, B, _, k): Maybe<&2, Read<B>>}
  {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a value of one field reads back
def Code.one_read(
  ~A: Data,
  ~T: Data,
  ~ca: Codec(A),
  mk: A -> T,
  a: A,
  r: List<&2, U32>
) -> {
  Code.one.read(
    ~A,
    ~T,
    ~Codec.dec(A, ca),
    mk,
    Codec.enc(A, ca)(a)(r)
  )
    == Some{Read{mk(a), r}}: Maybe<&2, Read<T>>
}:
  Equal.sym(
    Maybe<&2, Read<T>>,
    Some{Read{mk(a), r}},
    Code.one.read(~A, ~T, ~Codec.dec(A, ca), mk, Codec.enc(A, ca)(a)(r)),
    Read.then_some(
      A,
      T,
      Codec.dec(A, ca)(Codec.enc(A, ca)(a)(r)),
      x => r2 => Some{Read{mk(x), r2}},
      a,
      r,
      Codec.laws(A, ca)(a)(r)
    )
  )

# a value of two fields reads back
def Code.two_read(
  ~A: Data,
  ~B: Data,
  ~T: Data,
  ~ca: Codec(A),
  ~cb: Codec(B),
  mk: A -> B -> T,
  +a: A,
  +b: B,
  +r: List<&2, U32>
) -> {
  Code.two.read(
    ~A,
    ~B,
    ~T,
    ~Codec.dec(A, ca),
    ~Codec.dec(B, cb),
    mk,
    Codec.enc(A, ca)(a)(Codec.enc(B, cb)(b)(r))
  )
    == Some{Read{mk(a)(b), r}}: Maybe<&2, Read<T>>
}:
  rb = Codec.enc(B, cb)(b)(r)
  %Read.then_some(
    A,
    T,
    Codec.dec(A, ca)(Codec.enc(A, ca)(a)(rb)),
    x => r1 => Code.one.read(~B, ~T, ~Codec.dec(B, cb), mk(x), r1),
    a,
    rb,
    Codec.laws(A, ca)(a)(rb)
  ): {_ == Some{Read{mk(a)(b), r}}: Maybe<&2, Read<T>>}
  Code.one_read(~B, ~T, ~cb, mk(a), b, r)

# a value of three fields reads back
def Code.three_read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~T: Data,
  ~ca: Codec(A),
  ~cb: Codec(B),
  ~cc: Codec(C),
  mk: A -> B -> C -> T,
  +a: A,
  +b: B,
  +c: C,
  +r: List<&2, U32>
) -> {
  Code.three.read(
    ~A,
    ~B,
    ~C,
    ~T,
    ~Codec.dec(A, ca),
    ~Codec.dec(B, cb),
    ~Codec.dec(C, cc),
    mk,
    Codec.enc(A, ca)(a)(Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(r)))
  )
    == Some{Read{mk(a)(b)(c), r}}: Maybe<&2, Read<T>>
}:
  rb = Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(r))
  %Read.then_some(
    A,
    T,
    Codec.dec(A, ca)(Codec.enc(A, ca)(a)(rb)),
    x => r1 => Code.two.read(~B, ~C, ~T, ~Codec.dec(B, cb), ~Codec.dec(C, cc), mk(x), r1),
    a,
    rb,
    Codec.laws(A, ca)(a)(rb)
  ): {_ == Some{Read{mk(a)(b)(c), r}}: Maybe<&2, Read<T>>}
  Code.two_read(~B, ~C, ~T, ~cb, ~cc, mk(a), b, c, r)

# a value of four fields reads back
def Code.four_read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~D: Data,
  ~T: Data,
  ~ca: Codec(A),
  ~cb: Codec(B),
  ~cc: Codec(C),
  ~cd: Codec(D),
  mk: A -> B -> C -> D -> T,
  +a: A,
  +b: B,
  +c: C,
  +d: D,
  +r: List<&2, U32>
) -> {
  Code.four.read(
    ~A,
    ~B,
    ~C,
    ~D,
    ~T,
    ~Codec.dec(A, ca),
    ~Codec.dec(B, cb),
    ~Codec.dec(C, cc),
    ~Codec.dec(D, cd),
    mk,
    Codec.enc(A, ca)(a)(Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(Codec.enc(D, cd)(d)(r))))
  )
    == Some{Read{mk(a)(b)(c)(d), r}}: Maybe<&2, Read<T>>
}:
  rb = Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(Codec.enc(D, cd)(d)(r)))
  %Read.then_some(
    A,
    T,
    Codec.dec(A, ca)(Codec.enc(A, ca)(a)(rb)),
    x => r1 => Code.three.read(
      ~B,
      ~C,
      ~D,
      ~T,
      ~Codec.dec(B, cb),
      ~Codec.dec(C, cc),
      ~Codec.dec(D, cd),
      mk(x),
      r1
    ),
    a,
    rb,
    Codec.laws(A, ca)(a)(rb)
  ): {_ == Some{Read{mk(a)(b)(c)(d), r}}: Maybe<&2, Read<T>>}
  Code.three_read(~B, ~C, ~D, ~T, ~cb, ~cc, ~cd, mk(a), b, c, d, r)

# a value of five fields reads back
def Code.five_read(
  ~A: Data,
  ~B: Data,
  ~C: Data,
  ~D: Data,
  ~E: Data,
  ~T: Data,
  ~ca: Codec(A),
  ~cb: Codec(B),
  ~cc: Codec(C),
  ~cd: Codec(D),
  ~ce: Codec(E),
  mk: A -> B -> C -> D -> E -> T,
  +a: A,
  +b: B,
  +c: C,
  +d: D,
  +e: E,
  +r: List<&2, U32>
) -> {
  Code.five.read(
    ~A,
    ~B,
    ~C,
    ~D,
    ~E,
    ~T,
    ~Codec.dec(A, ca),
    ~Codec.dec(B, cb),
    ~Codec.dec(C, cc),
    ~Codec.dec(D, cd),
    ~Codec.dec(E, ce),
    mk,
    Codec.enc(A, ca)(a)(Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(Codec.enc(D, cd)(d)(Codec.enc(E, ce)(e)(r)))))
  )
    == Some{Read{mk(a)(b)(c)(d)(e), r}}: Maybe<&2, Read<T>>
}:
  rb = Codec.enc(B, cb)(b)(Codec.enc(C, cc)(c)(Codec.enc(D, cd)(d)(Codec.enc(E, ce)(e)(r))))
  %Read.then_some(
    A,
    T,
    Codec.dec(A, ca)(Codec.enc(A, ca)(a)(rb)),
    x => r1 => Code.four.read(
      ~B,
      ~C,
      ~D,
      ~E,
      ~T,
      ~Codec.dec(B, cb),
      ~Codec.dec(C, cc),
      ~Codec.dec(D, cd),
      ~Codec.dec(E, ce),
      mk(x),
      r1
    ),
    a,
    rb,
    Codec.laws(A, ca)(a)(rb)
  ): {_ == Some{Read{mk(a)(b)(c)(d)(e), r}}: Maybe<&2, Read<T>>}
  Code.four_read(~B, ~C, ~D, ~E, ~T, ~cb, ~cc, ~cd, ~ce, mk(a), b, c, d, e, r)

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a bit reads back
def Code.bool_read(b: Bool, r: List<&2, U32>) -> {Code.bool.read(Code.bool(b, r)) == Some{Read{b, r}}: Maybe<&2, Read<Bool>>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# a character reads back
def Code.char_read(c: Char, r: List<&2, U32>) -> {Code.char.read(Code.char(c, r)) == Some{Read{c, r}}: Maybe<&2, Read<Char>>}:
  match c:
    case Chr{x}:
      {==}

# the code of tokens
def Code.token.codec() -> Codec(U32):
  (Code.token, (Code.token.read, x => r => {==}))

# the code of bits
def Code.bool.codec() -> Codec(Bool):
  (Code.bool, (Code.bool.read, b => r => Code.bool_read(b, r)))

# the code of characters
def Code.char.codec() -> Codec(Char):
  (Code.char, (Code.char.read, c => r => Code.char_read(c, r)))

# the code of texts
def Code.text.codec() -> Codec(String):
  (Code.text, (Code.text.read, x => r => Code.text_read(x, r)))

# the code of values of c, if any
def Code.maybe.codec(~A: Data, ~c: Codec(A)) -> Codec(Maybe<&2, A>):
  (
    m => r => Code.maybe(~A, ~Codec.enc(A, c), m, r),
    (
      ts => Code.maybe.read(~A, ~Codec.dec(A, c), ts),
      m => r => Code.maybe_read(~A, ~Codec.enc(A, c), ~Codec.dec(A, c), Codec.laws(A, c), m, r)
    )
  )

# the code of lists of values of c
def Code.list.codec(~A: Data, ~c: Codec(A)) -> Codec(List<&2, A>):
  (
    xs => r => Code.list(~A, ~Codec.enc(A, c), xs, r),
    (
      ts => Code.list.read(~A, ~Codec.dec(A, c), ts),
      xs => r => Code.list_read(~A, ~Codec.enc(A, c), ~Codec.dec(A, c), ~Codec.laws(A, c), xs, r)
    )
  )

# the code of words
def Code.words.codec() -> Codec(List<&2, U32>):
  Code.list.codec(~U32, ~Code.token.codec())

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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# two values with the same code are the same, when the code reads back
def Code.is_eq_sound(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  ~laws: Code.Laws(A, enc, dec),
  +a: A,
  +b: A
) -> {Code.is_eq(~A, ~enc, a, b) == True{}: Bool} -> {a == b: A}:
  dec1 = dec(enc(b)([]))
  h => Equal.trans(A, a, Code.read_value(A, dec1, a), b, (
      %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), enc(a)([]), enc(b)([]))(h): {a == Code.read_value(A, dec(_), a): A}
      %Equal.sym(Maybe<&2, Read<A>>, dec(enc(a)([])), Some{Read{a, []}}, laws(a)([])): {a == Code.read_value(A, _, a): A}
      {==}), (
      %Equal.sym(Maybe<&2, Read<A>>, dec1, Some{Read{b, []}}, laws(b)([])): {Code.read_value(A, _, a) == b: A}
      {==}))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# equality of codes is an equality
def Code.eq_laws(~A: Data, ~c: Codec(A)) -> Shared.Eq.Laws(A, Code.is_eq(~A, ~Codec.enc(A, c))):
  (
    a => Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Codec.enc(A, c)(a)([])),
    a => b => Code.is_eq_sound(~A, ~Codec.enc(A, c), ~Codec.dec(A, c), ~Codec.laws(A, c), a, b)
  )

# Whole codes
# -----------

# the value of m, when ws is its code
def Code.whole.check(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  m: Maybe<&2, A>,
  ws: List<&2, U32>
) -> Maybe<&2, A>:
  match m:
    case None{}:
      None{}
    case Some{+a}:
      Bool.pick(
        Maybe<&2, A>,
        Shared.List.is_eq(~U32, ~U32.is_eq, enc(a)([]), ws),
        Some{a},
        None{}
      )

# the value whose code is exactly the words ws
def Code.whole.read(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  +ws: List<&2, U32>
) -> Maybe<&2, A>:
  Code.whole.check(~A, ~enc, Read.whole(A, dec(ws)), ws)

# the value whose code m holds, if m holds words
def Code.whole.of(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Read<A>>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, A>:
  match m:
    case None{}:
      None{}
    case Some{ws}:
      Code.whole.read(~A, ~enc, ~dec, ws)

# the code of a value, alone, reads whole as the value
law Code.whole_read:
  for ~A: Data
  for ~enc: A -> List<&2, U32> -> List<&2, U32>
  for ~dec: List<&2, U32> -> Maybe<&2, Read<A>>
  for ~laws: Code.Laws(A, enc, dec)
  for +a: A
  {Code.whole.read(~A, ~enc, ~dec, enc(a)([])) == Some{a}: Maybe<&2, A>}

def Code.whole_read(ty, enc, dec, laws, a):
  %Equal.sym(Maybe<&2, Read<ty>>, dec(enc(a)([])), Some{Read{a, []}}, laws(a)([])): {
    Code.whole.check(~ty, ~enc, Read.whole(ty, _), enc(a)([])) == Some{a}: Maybe<&2, ty>
  }
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, enc(a)([]), enc(a)([])),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), enc(a)([]))
  ): {Bool.pick(Maybe<&2, ty>, _, Some{a}, None{}) == Some{a}: Maybe<&2, ty>}
  {==}

# Code.whole_back once it is known whether b's code is ws (t)
def Code.whole_back.at(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  b: A,
  ws: List<&2, U32>,
  -a: A,
  t: Bool,
  et: {Shared.List.is_eq(~U32, ~U32.is_eq, enc(b)([]), ws) == t: Bool}
) -> {Bool.pick(Maybe<&2, A>, t, Some{b}, None{}) == Some{a}: Maybe<&2, A>} -> {enc(a)([]) == ws: List<&2, U32>}:
  match t:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(A, b, a, e): {enc(_)([]) == ws: List<&2, U32>}
        Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), enc(b)([]), ws)(et)
    case False{}:
      e => Empty.absurd({enc(a)([]) == ws: List<&2, U32>}, Shared.Maybe.none_ne_some(A, a, e))

# Code.whole_back for the value m that the read gave
def Code.whole_back.of(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  m: Maybe<&2, A>,
  +ws: List<&2, U32>,
  -a: A
) -> {Code.whole.check(~A, ~enc, m, ws) == Some{a}: Maybe<&2, A>} -> {enc(a)([]) == ws: List<&2, U32>}:
  match m:
    case None{}:
      e => Empty.absurd({enc(a)([]) == ws: List<&2, U32>}, Shared.Maybe.none_ne_some(A, a, e))
    case Some{+b}:
      Code.whole_back.at(
        ~A,
        ~enc,
        b,
        ws,
        a,
        Shared.List.is_eq(~U32, ~U32.is_eq, enc(b)([]), ws),
        {==}
      )

# words that read whole as a value are its code: each value has one code
law Code.whole_back:
  for ~A: Data
  for ~enc: A -> List<&2, U32> -> List<&2, U32>
  for ~dec: List<&2, U32> -> Maybe<&2, Read<A>>
  for +ws: List<&2, U32>
  for a: A
  {Code.whole.read(~A, ~enc, ~dec, ws) == Some{a}: Maybe<&2, A>} -> {enc(a)([]) == ws: List<&2, U32>}

def Code.whole_back(ty, enc, dec, ws, a):
  Code.whole_back.of(~ty, ~enc, Read.whole(ty, dec(ws)), ws, a)
