import Base

# Hashes
# ------
# SHA-256 (FIPS 180-4) of a list of 32-bit words, read as their bytes from the
# highest: the hash of the codes that nodes store and send. A node keeps data
# under its hash and checks the hash of what it reads, so data that does not
# match its key is never believed.

# a hash: its eight words
type Hash is Data:
  Hash{h0: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32}

# the words of a block, the next one first
type Block is Data:
  Block{
    w0: U32,
    w1: U32,
    w2: U32,
    w3: U32,
    w4: U32,
    w5: U32,
    w6: U32,
    w7: U32,
    w8: U32,
    w9: U32,
    w10: U32,
    w11: U32,
    w12: U32,
    w13: U32,
    w14: U32,
    w15: U32
  }

# the round constants
def Sha.k() -> List<&2, U32>:
  [
    1116352408,
    1899447441,
    3049323471,
    3921009573,
    961987163,
    1508970993,
    2453635748,
    2870763221,
    3624381080,
    310598401,
    607225278,
    1426881987,
    1925078388,
    2162078206,
    2614888103,
    3248222580,
    3835390401,
    4022224774,
    264347078,
    604807628,
    770255983,
    1249150122,
    1555081692,
    1996064986,
    2554220882,
    2821834349,
    2952996808,
    3210313671,
    3336571891,
    3584528711,
    113926993,
    338241895,
    666307205,
    773529912,
    1294757372,
    1396182291,
    1695183700,
    1986661051,
    2177026350,
    2456956037,
    2730485921,
    2820302411,
    3259730800,
    3345764771,
    3516065817,
    3600352804,
    4094571909,
    275423344,
    430227734,
    506948616,
    659060556,
    883997877,
    958139571,
    1322822218,
    1537002063,
    1747873779,
    1955562222,
    2024104815,
    2227730452,
    2361852424,
    2428436474,
    2756734187,
    3204031479,
    3329325298
  ]

# x turned right by n (and left by m = 32 - n)
def Sha.rotr(+x: U32, n: Nat, m: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, m))

# the small sigma 0 of x
def Sha.s0(+x: U32) -> U32:
  U32.xor(Sha.rotr(x, 7n, 25n), U32.xor(Sha.rotr(x, 18n, 14n), U32.shrn(x, 3n)))

# the small sigma 1 of x
def Sha.s1(+x: U32) -> U32:
  U32.xor(Sha.rotr(x, 17n, 15n), U32.xor(Sha.rotr(x, 19n, 13n), U32.shrn(x, 10n)))

# the big sigma 0 of x
def Sha.b0(+x: U32) -> U32:
  U32.xor(Sha.rotr(x, 2n, 30n), U32.xor(Sha.rotr(x, 13n, 19n), Sha.rotr(x, 22n, 10n)))

# the big sigma 1 of x
def Sha.b1(+x: U32) -> U32:
  U32.xor(Sha.rotr(x, 6n, 26n), U32.xor(Sha.rotr(x, 11n, 21n), Sha.rotr(x, 25n, 7n)))

# the block after its first word: the next word of the schedule at its end
def Block.next(b: Block) -> Block:
  match b:
    case Block{w0, +w1, w2, w3, w4, w5, w6, w7, w8, +w9, w10, w11, w12, w13, +w14, w15}:
      Block{
        w1,
        w2,
        w3,
        w4,
        w5,
        w6,
        w7,
        w8,
        w9,
        w10,
        w11,
        w12,
        w13,
        w14,
        w15,
        (Sha.s1(w14) + w9 + Sha.s0(w1) + w0: U32)
      }

# the first word of a block
def Block.first(b: Block) -> U32:
  match b:
    case Block{w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15}:
      w0

# the hash h after the rounds with the constants ks and the schedule b
def Sha.rounds(ks: List<&2, U32>, +b: Block, h: Hash) -> Hash:
  match ks h:
    case Nil{} x:
      x
    case Con{k, r} Hash{+a, +bb, +c, d, +e, +f, +g, hh}:
      +t1 = (
        hh + Sha.b1(e) + U32.xor(U32.and(e, f), U32.and(U32.not(e), g)) + k + Block.first(b): U32
      )
      t2 = (Sha.b0(a) + U32.xor(U32.and(a, bb), U32.xor(U32.and(a, c), U32.and(bb, c))): U32)
      Sha.rounds(r, Block.next(b), Hash{(t1 + t2: U32), a, bb, c, (d + t1: U32), e, f, g})

# the sum of two hashes, word by word
def Hash.add(x: Hash, y: Hash) -> Hash:
  match x y:
    case Hash{a0, b0, c0, d0, e0, f0, g0, h0} Hash{a1, b1, c1, d1, e1, f1, g1, h1}:
      Hash{
        (a0 + a1: U32),
        (b0 + b1: U32),
        (c0 + c1: U32),
        (d0 + d1: U32),
        (e0 + e1: U32),
        (f0 + f1: U32),
        (g0 + g1: U32),
        (h0 + h1: U32)
      }

# the hash h after the block b
def Sha.block(+h: Hash, b: Block) -> Hash:
  Hash.add(h, Sha.rounds(Sha.k(), b, h))

# a block of 16 words, if ws holds them
def Block.of(ws: List<&2, U32>) -> Maybe<&2, Block>:
  match ws:
    case Con{
      w0,
      Con{
        w1,
        Con{
          w2,
          Con{
            w3,
            Con{
              w4,
              Con{
                w5,
                Con{
                  w6,
                  Con{
                    w7,
                    Con{
                      w8,
                      Con{w9, Con{w10, Con{w11, Con{w12, Con{w13, Con{w14, Con{w15, Nil{}}}}}}}}
                    }
                  }
                }
              }
            }
          }
        }
      }
    }:
      Some{Block{w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15}}
    case _:
      None{}

# the words after the first n
def Sha.skip(n: Nat, ws: List<&2, U32>) -> List<&2, U32>:
  match n ws:
    case 0n w:
      w
    case 1n+p Nil{}:
      []
    case 1n+p Con{x, r}:
      Sha.skip(p, r)

# n zero words, then rest
def Sha.zeros(n: Nat, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      0 <> Sha.zeros(p, rest)

# the padded end of a message whose last words are ws (fewer than 16, r of
# them) and whose length is len words: a one bit, zeros, then the length in
# bits, as one block or two
def Sha.pad(ws: List<&2, U32>, +r: Nat, +len: U32) -> List<&2, U32>:
  List.append(
    &2,
    U32,
    ws,
    2147483648
      <> Sha.zeros(
        Bool.pick(Nat, Nat.is_le(r, 13n), Nat.sub(13n, r), Nat.sub(29n, r)),
        [U32.shrn(len, 27n), U32.shln(len, 5n)]
      )
  )

# the hash h after a second block m, if any
def Sha.last.two(m: Maybe<&2, Block>, h: Hash) -> Hash:
  match m:
    case Some{b}:
      Sha.block(h, b)
    case None{}:
      h

# the hash h after the first block m of the padded end ws, then its second
def Sha.last.of(m: Maybe<&2, Block>, ws: List<&2, U32>, h: Hash) -> Hash:
  match m:
    case Some{b}:
      Sha.last.two(Block.of(Sha.skip(16n, ws)), Sha.block(h, b))
    case None{}:
      h

# Sha.go once the first block m of ws is known (none: fewer than 16 words left)
def Sha.go.of(f: Nat, h: Hash, +ws: List<&2, U32>, done: U32, m: Maybe<&2, Block>) -> Hash:
  match f m:
    case 1n+p Some{b}:
      Sha.go.of(
        p,
        Sha.block(h, b),
        Sha.skip(16n, ws),
        (done + 16: U32),
        Block.of(List.take(&2, U32, Sha.skip(16n, ws), 16n))
      )
    case g w:
      +r = List.length(&2, U32, ws)
      +end = Sha.pad(ws, r, (done + U32.from_nat(r): U32))
      Sha.last.of(Block.of(List.take(&2, U32, end, 16n)), end, h)

# the SHA-256 hash of the words ws
def Sha.hash(+ws: List<&2, U32>) -> Hash:
  Sha.go.of(
    List.length(&2, U32, ws),
    Hash{
      1779033703,
      3144134277,
      1013904242,
      2773480762,
      1359893119,
      2600822924,
      528734635,
      1541459225
    },
    ws,
    0,
    Block.of(List.take(&2, U32, ws, 16n))
  )
