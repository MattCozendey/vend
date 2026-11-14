import Base
import ./shared/code.bend as Codes
import ./shared/shared.bend as Shared

# Packed bytes
# ------------
# Content is kept packed: a word holds four bytes, the first one highest, so
# a byte costs a quarter of a word, not a whole one. A piece of content is its
# length in bytes, as a count, then its words; the last word is filled with
# zeros. So packed pieces, one after the other, read back without a mark
# between them.

# the word of the bytes a, b, c and d, the first highest: the low eight bits
# of each
def Pack.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, x}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, y}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, z}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, q}}}}}}}}}:
      U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# the words of the bytes bs, four in each
def Pack.words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      []
    case Con{a, Nil{}}:
      [Pack.word(a, 0, 0, 0)]
    case Con{a, Con{b, Nil{}}}:
      [Pack.word(a, b, 0, 0)]
    case Con{a, Con{b, Con{c, Nil{}}}}:
      [Pack.word(a, b, c, 0)]
    case Con{a, Con{b, Con{c, Con{d, rest}}}}:
      Pack.word(a, b, c, d) <> Pack.words(rest)

# the piece bs, packed: its length, then its words
def Pack.piece(+bs: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.count(List.length(&2, U32, bs), Pack.words(bs))

# each of the pieces ps, packed
def Pack.pieces(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      []
    case Con{x, rest}:
      Pack.piece(x) <> Pack.pieces(rest)

# the four bytes of the word w, the highest first
def Pack.quad(w: U32) -> List<&2, U32>:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      [Shared.Byte.of(w24, w25, w26, w27, w28, w29, w30, w31), Shared.Byte.of(w16, w17, w18, w19, w20, w21, w22, w23), Shared.Byte.of(w8, w9, w10, w11, w12, w13, w14, w15), Shared.Byte.of(w0, w1, w2, w3, w4, w5, w6, w7)]

# the first n bytes of the word w (four at most), then rest
def Pack.bytes(n: Nat, w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, Pack.quad(w), n), rest)

# what a read of packed pieces expects next: the digits of a length, after
# those that sum to acc, or the bytes of a piece, of which left + 1 remain
type At is Data:
  At.Length{acc: Nat}
  At.Body{left: Nat}

# a read at the start of the body of a piece of n bytes
def At.of(n: Nat) -> At:
  match n:
    case 0n:
      At.Length{0n}
    case 1n+p:
      At.Body{p}

# the bytes of the packed pieces ws, read from at
def Pack.read(ws: List<&2, U32>, at: At) -> List<&2, U32>:
  match ws at:
    case Nil{} a:
      []
    case Con{+w, +rest} At.Length{+acc}:
      Shared.Bool.when(
        List<&2, U32>,
        U32.is_eq(w, 4294967295),
        u => Pack.read(rest, At.Length{Nat.add(acc, U32.to_nat(w))}),
        u => Pack.read(rest, At.of(Nat.add(acc, U32.to_nat(w))))
      )
    case Con{w, rest} At.Body{+k}:
      Pack.bytes(1n+k, w, Pack.read(rest, At.of(Nat.sub(k, 3n))))

# each element of each of the pieces ps is a byte
def Pack.all_fit(ps: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{x, rest}:
      List.all.if(u => Pack.all_fit(rest), Shared.Bytes.is_bytes(x))

# the four bytes of each of the words ws: words as bytes
def Pack.unpack(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{w, rest}:
      List.append(&2, U32, Pack.quad(w), Pack.unpack(rest))

# Laws
# ----

# the bytes of the word of four bytes are their low eight bits
def Pack.quad_word(
  a: U32,
  b: U32,
  c: U32,
  d: U32
) -> {
  Pack.quad(Pack.word(a, b, c, d))
    == [Shared.Byte.low(a), Shared.Byte.low(b), Shared.Byte.low(c), Shared.Byte.low(d)]: List<&2, U32>
}:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, x}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, y}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, z}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, q}}}}}}}}}:
      {==}

# the first of a list that is all bytes is a byte
def Pack.fit_first(
  +a: U32,
  +rest: List<&2, U32>
) -> {Shared.Bytes.is_bytes(a <> rest) == True{}: Bool} -> {Shared.Bytes.is_bytes([a]) == True{}: Bool}:
  match a:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, +h}}}}}}}}}:
      e => Shared.List.all.if_both(Shared.Word.is_zero(24n, h), u => True{})(
        Shared.List.all.if_hit(Shared.Word.is_zero(24n, h), u => Shared.Bytes.is_bytes(rest))(e)
      )({==})

# the rest of a list that is all bytes is all bytes
def Pack.fit_rest(
  +a: U32,
  +rest: List<&2, U32>
) -> {Shared.Bytes.is_bytes(a <> rest) == True{}: Bool} -> {Shared.Bytes.is_bytes(rest) == True{}: Bool}:
  match a:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, +h}}}}}}}}}:
      e => Shared.List.all.if_rest(Shared.Word.is_zero(24n, h), u => Shared.Bytes.is_bytes(rest))(e)

# Pack.count_read one digit on, once it is known whether c + 1 is the top (b)
def Pack.count_read.next(
  +p: Nat,
  +c: U32,
  +r: List<&2, U32>,
  +acc: Nat,
  h: {U32.is_eq(c, 4294967295) == False{}: Bool},
  b: Bool,
  eb: {U32.is_eq(U32.inc(c), 4294967295) == b: Bool},
  ih: @d: U32 -> {U32.is_eq(d, 4294967295) == False{}: Bool} -> @a: Nat -> {
    Pack.read(Codes.Code.count.go(p, d, r), At.Length{a})
      == Pack.read(r, At.of(Nat.add(a, Nat.add(U32.to_nat(d), p)))): List<&2, U32>
  }
) -> {
  Pack.read(
    Shared.Bool.when(
      List<&2, U32>,
      b,
      u => U32.inc(c) <> Codes.Code.count.go(p, 0, r),
      u => Codes.Code.count.go(p, U32.inc(c), r)
    ),
    At.Length{acc}
  )
    == Pack.read(r, At.of(Nat.add(acc, Nat.add(U32.to_nat(c), 1n+p)))): List<&2, U32>
}:
  match b:
    case True{}:
      %Equal.sym(
        Nat,
        Nat.add(U32.to_nat(c), 1n+p),
        1n+Nat.add(U32.to_nat(c), p),
        Shared.Nat.add_succ(U32.to_nat(c), p)
      ): {
        Pack.read(U32.inc(c) <> Codes.Code.count.go(p, 0, r), At.Length{acc})
          == Pack.read(r, At.of(Nat.add(acc, _))): List<&2, U32>
      }
      %Shared.U32.inc_to_nat(c)(h): {
        Pack.read(U32.inc(c) <> Codes.Code.count.go(p, 0, r), At.Length{acc})
          == Pack.read(r, At.of(Nat.add(acc, Nat.add(_, p)))): List<&2, U32>
      }
      %Equal.sym(Bool, U32.is_eq(U32.inc(c), 4294967295), True{}, eb): {
        Shared.Bool.when(
          List<&2, U32>,
          _,
          u => Pack.read(Codes.Code.count.go(p, 0, r), At.Length{Nat.add(acc, U32.to_nat(U32.inc(c)))}),
          u => Pack.read(Codes.Code.count.go(p, 0, r), At.of(Nat.add(acc, U32.to_nat(U32.inc(c)))))
        )
          == Pack.read(r, At.of(Nat.add(acc, Nat.add(U32.to_nat(U32.inc(c)), p)))): List<&2, U32>
      }
      %Equal.sym(
        List<&2, U32>,
        Pack.read(Codes.Code.count.go(p, 0, r), At.Length{Nat.add(acc, U32.to_nat(U32.inc(c)))}),
        Pack.read(r, At.of(Nat.add(Nat.add(acc, U32.to_nat(U32.inc(c))), p))),
        ih(0)({==})(Nat.add(acc, U32.to_nat(U32.inc(c))))
      ): {_ == Pack.read(r, At.of(Nat.add(acc, Nat.add(U32.to_nat(U32.inc(c)), p)))): List<&2, U32>}
      %Shared.Nat.add_assoc(acc, U32.to_nat(U32.inc(c)), p): {
        Pack.read(r, At.of(Nat.add(Nat.add(acc, U32.to_nat(U32.inc(c))), p)))
          == Pack.read(r, At.of(_)): List<&2, U32>
      }
      {==}
    case False{}:
      %Equal.sym(
        Nat,
        Nat.add(U32.to_nat(c), 1n+p),
        1n+Nat.add(U32.to_nat(c), p),
        Shared.Nat.add_succ(U32.to_nat(c), p)
      ): {
        Pack.read(Codes.Code.count.go(p, U32.inc(c), r), At.Length{acc})
          == Pack.read(r, At.of(Nat.add(acc, _))): List<&2, U32>
      }
      %Shared.U32.inc_to_nat(c)(h): {
        Pack.read(Codes.Code.count.go(p, U32.inc(c), r), At.Length{acc})
          == Pack.read(r, At.of(Nat.add(acc, Nat.add(_, p)))): List<&2, U32>
      }
      ih(U32.inc(c))(eb)(acc)

# the digits of a count, from the digit c below the top, are read as their sum
# after acc
def Pack.count_read(
  +n: Nat,
  +c: U32,
  +r: List<&2, U32>,
  +acc: Nat,
  h: {U32.is_eq(c, 4294967295) == False{}: Bool}
) -> {
  Pack.read(Codes.Code.count.go(n, c, r), At.Length{acc})
    == Pack.read(r, At.of(Nat.add(acc, Nat.add(U32.to_nat(c), n)))): List<&2, U32>
}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(U32.to_nat(c), 0n), U32.to_nat(c), Shared.Nat.add_zero(U32.to_nat(c))): {
        Pack.read(c <> r, At.Length{acc}) == Pack.read(r, At.of(Nat.add(acc, _))): List<&2, U32>
      }
      %Equal.sym(Bool, U32.is_eq(c, 4294967295), False{}, h): {
        Shared.Bool.when(
          List<&2, U32>,
          _,
          u => Pack.read(r, At.Length{Nat.add(acc, U32.to_nat(c))}),
          u => Pack.read(r, At.of(Nat.add(acc, U32.to_nat(c))))
        )
          == Pack.read(r, At.of(Nat.add(acc, U32.to_nat(c)))): List<&2, U32>
      }
      {==}
    case 1n+p:
      Pack.count_read.next(
        p,
        c,
        r,
        acc,
        h,
        U32.is_eq(U32.inc(c), 4294967295),
        {==},
        d => hd => a => Pack.count_read(p, d, r, a, hd)
      )

# the words of bytes, then r, read as the body of a piece of their length,
# are the bytes, then what r reads as
def Pack.body_read(
  +bs: List<&2, U32>,
  +r: List<&2, U32>
) -> {Shared.Bytes.is_bytes(bs) == True{}: Bool} -> {
  Pack.read(List.append(&2, U32, Pack.words(bs), r), At.of(List.length(&2, U32, bs)))
    == List.append(&2, U32, bs, Pack.read(r, At.Length{0n})): List<&2, U32>
}:
  match bs:
    case Nil{}:
      e => {==}
    case Con{+a, Nil{}}:
      +e =>
        %Equal.sym(
          List<&2, U32>,
          Pack.quad(Pack.word(a, 0, 0, 0)),
          [Shared.Byte.low(a), Shared.Byte.low(0), Shared.Byte.low(0), Shared.Byte.low(0)],
          Pack.quad_word(a, 0, 0, 0)
        ): {
          List.append(&2, U32, List.take(&2, U32, _, 1n), Pack.read(r, At.of(Nat.sub(0n, 3n))))
            == a <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(a), a, Shared.Byte.low_eq(a)(e)): {
          _ <> Pack.read(r, At.Length{0n}) == a <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        {==}
    case Con{+a, Con{+b, Nil{}}}:
      +e =>
        fa = Pack.fit_first(a, [b])(e)
        eb = Pack.fit_first(b, [])(Pack.fit_rest(a, [b])(e))
        %Equal.sym(
          List<&2, U32>,
          Pack.quad(Pack.word(a, b, 0, 0)),
          [Shared.Byte.low(a), Shared.Byte.low(b), Shared.Byte.low(0), Shared.Byte.low(0)],
          Pack.quad_word(a, b, 0, 0)
        ): {
          List.append(&2, U32, List.take(&2, U32, _, 2n), Pack.read(r, At.of(Nat.sub(1n, 3n))))
            == a <> b <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(a), a, Shared.Byte.low_eq(a)(fa)): {
          _ <> Shared.Byte.low(b) <> Pack.read(r, At.Length{0n}) == a <> b <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(b), b, Shared.Byte.low_eq(b)(eb)): {
          a <> _ <> Pack.read(r, At.Length{0n}) == a <> b <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        {==}
    case Con{+a, Con{+b, Con{+c, Nil{}}}}:
      +e =>
        fa = Pack.fit_first(a, [b, c])(e)
        +er = Pack.fit_rest(a, [b, c])(e)
        fb = Pack.fit_first(b, [c])(er)
        fc = Pack.fit_first(c, [])(Pack.fit_rest(b, [c])(er))
        %Equal.sym(
          List<&2, U32>,
          Pack.quad(Pack.word(a, b, c, 0)),
          [Shared.Byte.low(a), Shared.Byte.low(b), Shared.Byte.low(c), Shared.Byte.low(0)],
          Pack.quad_word(a, b, c, 0)
        ): {
          List.append(&2, U32, List.take(&2, U32, _, 3n), Pack.read(r, At.of(Nat.sub(2n, 3n))))
            == a <> b <> c <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(a), a, Shared.Byte.low_eq(a)(fa)): {
          _ <> Shared.Byte.low(b) <> Shared.Byte.low(c) <> Pack.read(r, At.Length{0n})
            == a <> b <> c <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(b), b, Shared.Byte.low_eq(b)(fb)): {
          a <> _ <> Shared.Byte.low(c) <> Pack.read(r, At.Length{0n})
            == a <> b <> c <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(c), c, Shared.Byte.low_eq(c)(fc)): {
          a <> b <> _ <> Pack.read(r, At.Length{0n}) == a <> b <> c <> Pack.read(r, At.Length{0n}): List<&2, U32>
        }
        {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, +rest}}}}:
      +e =>
        fa = Pack.fit_first(a, b <> c <> d <> rest)(e)
        +e1 = Pack.fit_rest(a, b <> c <> d <> rest)(e)
        fb = Pack.fit_first(b, c <> d <> rest)(e1)
        +e2 = Pack.fit_rest(b, c <> d <> rest)(e1)
        fc = Pack.fit_first(c, d <> rest)(e2)
        +e3 = Pack.fit_rest(c, d <> rest)(e2)
        fd = Pack.fit_first(d, rest)(e3)
        fr = Pack.fit_rest(d, rest)(e3)
        +tail = Pack.read(List.append(&2, U32, Pack.words(rest), r), At.of(List.length(&2, U32, rest)))
        %Equal.sym(
          Nat,
          Nat.sub(List.length(&2, U32, rest), 0n),
          List.length(&2, U32, rest),
          Shared.Nat.sub_zero(List.length(&2, U32, rest))
        ): {
          List.append(
            &2,
            U32,
            List.take(&2, U32, Pack.quad(Pack.word(a, b, c, d)), 4n+List.length(&2, U32, rest)),
            Pack.read(List.append(&2, U32, Pack.words(rest), r), At.of(_))
          )
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(
          List<&2, U32>,
          Pack.quad(Pack.word(a, b, c, d)),
          [Shared.Byte.low(a), Shared.Byte.low(b), Shared.Byte.low(c), Shared.Byte.low(d)],
          Pack.quad_word(a, b, c, d)
        ): {
          List.append(&2, U32, List.take(&2, U32, _, 4n+List.length(&2, U32, rest)), tail)
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(
          List<&2, U32>,
          tail,
          List.append(&2, U32, rest, Pack.read(r, At.Length{0n})),
          Pack.body_read(rest, r)(fr)
        ): {
          Shared.Byte.low(a) <> Shared.Byte.low(b) <> Shared.Byte.low(c) <> Shared.Byte.low(d) <> _
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(a), a, Shared.Byte.low_eq(a)(fa)): {
          _ <> Shared.Byte.low(b) <> Shared.Byte.low(c) <> Shared.Byte.low(d) <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n}))
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(b), b, Shared.Byte.low_eq(b)(fb)): {
          a <> _ <> Shared.Byte.low(c) <> Shared.Byte.low(d) <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n}))
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(c), c, Shared.Byte.low_eq(c)(fc)): {
          a <> b <> _ <> Shared.Byte.low(d) <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n}))
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        %Equal.sym(U32, Shared.Byte.low(d), d, Shared.Byte.low_eq(d)(fd)): {
          a <> b <> c <> _ <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n}))
            == a <> b <> c <> d <> List.append(&2, U32, rest, Pack.read(r, At.Length{0n})): List<&2, U32>
        }
        {==}

# words as bytes pack back to the words
law Pack.words_unpack:
  for ws: List<&2, U32>
  {Pack.words(Pack.unpack(ws)) == ws: List<&2, U32>}

def Pack.words_unpack(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      %Pack.words_unpack(r): {
        Pack.words(List.append(&2, U32, Pack.quad(U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), Pack.unpack(r)))
          == U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> _: List<&2, U32>
      }
      {==}

# packed pieces read back as their bytes, one piece after the other
law Pack.read_pieces:
  for ps: List<&2, List<&2, U32>>
  {Pack.all_fit(ps) == True{}: Bool}
    -> {
      Pack.read(List.concat(&2, U32, Pack.pieces(ps)), At.Length{0n})
        == List.concat(&2, U32, ps): List<&2, U32>
    }

def Pack.read_pieces(ps):
  match ps:
    case Nil{}:
      e => {==}
    case Con{+bs, +rest}:
      +e =>
        fb = Shared.List.all.if_hit(Shared.Bytes.is_bytes(bs), u => Pack.all_fit(rest))(e)
        fr = Shared.List.all.if_rest(Shared.Bytes.is_bytes(bs), u => Pack.all_fit(rest))(e)
        +x = List.concat(&2, U32, Pack.pieces(rest))
        +w = Pack.words(bs)
        +n = List.length(&2, U32, bs)
        +goal = List.append(&2, U32, bs, List.concat(&2, U32, rest))
        %Equal.sym(
          List<&2, U32>,
          Codes.Code.count(n, w),
          Codes.Code.count.go(n, 0, w),
          Codes.Code.count_go(n, w)
        ): {Pack.read(List.append(&2, U32, _, x), At.Length{0n}) == goal: List<&2, U32>}
        %Equal.sym(
          List<&2, U32>,
          List.append(&2, U32, Codes.Code.count.go(n, 0, w), x),
          Codes.Code.count.go(n, 0, List.append(&2, U32, w, x)),
          Codes.Code.count_append(n, 0, w, x)
        ): {Pack.read(_, At.Length{0n}) == goal: List<&2, U32>}
        %Equal.sym(
          List<&2, U32>,
          Pack.read(Codes.Code.count.go(n, 0, List.append(&2, U32, w, x)), At.Length{0n}),
          Pack.read(List.append(&2, U32, w, x), At.of(Nat.add(0n, Nat.add(U32.to_nat(0), n)))),
          Pack.count_read(n, 0, List.append(&2, U32, w, x), 0n, {==})
        ): {_ == goal: List<&2, U32>}
        %Equal.sym(
          List<&2, U32>,
          Pack.read(List.append(&2, U32, w, x), At.of(n)),
          List.append(&2, U32, bs, Pack.read(x, At.Length{0n})),
          Pack.body_read(bs, x)(fb)
        ): {_ == goal: List<&2, U32>}
        %Equal.sym(
          List<&2, U32>,
          Pack.read(x, At.Length{0n}),
          List.concat(&2, U32, rest),
          Pack.read_pieces(rest)(fr)
        ): {List.append(&2, U32, bs, _) == goal: List<&2, U32>}
        {==}
