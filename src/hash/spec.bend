import Base
import ../shared/bytes.bend as Octets

# BLAKE3 in its default hash mode, as the BLAKE3 specification states it
# (https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf):
# section 2.1 (the IV and the flags), 2.2 (the compression function: G, the
# round, the message permutation), 2.4 (chunks of 1024 bytes in 64-byte
# blocks, the chunk counter) and 2.5 (the tree: the left subtree holds the
# largest power of two of chunks that leaves at least one byte for the
# right one; the root sets ROOT). An input past 2^32 chunks (4 TiB) is out
# of scope: the counter's high word is 0.

# eight words: a chaining value
type Cv8 is Data:
  Cv8{h0: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32}

# sixteen words: a message block
type Msg16 is Data:
  Msg16{
    m0: U32,
    m1: U32,
    m2: U32,
    m3: U32,
    m4: U32,
    m5: U32,
    m6: U32,
    m7: U32,
    m8: U32,
    m9: U32,
    m10: U32,
    m11: U32,
    m12: U32,
    m13: U32,
    m14: U32,
    m15: U32
  }

# sixteen words: the state of a compression
type St16 is Data:
  St16{
    s0: U32,
    s1: U32,
    s2: U32,
    s3: U32,
    s4: U32,
    s5: U32,
    s6: U32,
    s7: U32,
    s8: U32,
    s9: U32,
    s10: U32,
    s11: U32,
    s12: U32,
    s13: U32,
    s14: U32,
    s15: U32
  }

# a block: how many bytes it holds, and its words, padded with zeros
type Blk is Data:
  Blk{len: U32, words: Msg16}

# The last compression of a node, not yet done: a chunk's last block, or a
# parent's two children. The root sets ROOT on it; any other node takes
# its chaining value.
type Pending is Data:
  Pending{cv: Cv8, block: Msg16, counter: U32, len: U32, flags: U32}

# the IV, the same as SHA-256's
def Blake3.iv() -> Cv8:
  Cv8{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

# x rotated right by r bits, where l is 32 - r
def Blake3.rotr(+x: U32, r: Nat, l: Nat) -> U32:
  ((x >> r) .|. (x << l): U32)

# the message permutation: word i of the result is word p(i) of m, where p
# is [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def Blake3.permute(m: Msg16) -> Msg16:
  match m:
    case Msg16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}:
      Msg16{m2, m6, m3, m10, m7, m0, m4, m13, m1, m11, m12, m5, m9, m14, m15, m8}

# one round: G on the four columns, then on the four diagonals
def Blake3.round(st: St16, m: Msg16) -> St16:
  match st m:
    case St16{
      s0,
      s1,
      s2,
      s3,
      +s4,
      +s5,
      +s6,
      +s7,
      s8,
      s9,
      s10,
      s11,
      s12,
      s13,
      s14,
      s15
    } Msg16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}:
      +g0a1 = (s0 + s4 + m0: U32)
      +g0d1 = Blake3.rotr((s12 .^. g0a1: U32), 16n, 16n)
      +g0c1 = (s8 + g0d1: U32)
      +g0b1 = Blake3.rotr((s4 .^. g0c1: U32), 12n, 20n)
      +g0a2 = (g0a1 + g0b1 + m1: U32)
      +g0d2 = Blake3.rotr((g0d1 .^. g0a2: U32), 8n, 24n)
      +g0c2 = (g0c1 + g0d2: U32)
      +g0b2 = Blake3.rotr((g0b1 .^. g0c2: U32), 7n, 25n)
      +g1a1 = (s1 + s5 + m2: U32)
      +g1d1 = Blake3.rotr((s13 .^. g1a1: U32), 16n, 16n)
      +g1c1 = (s9 + g1d1: U32)
      +g1b1 = Blake3.rotr((s5 .^. g1c1: U32), 12n, 20n)
      +g1a2 = (g1a1 + g1b1 + m3: U32)
      +g1d2 = Blake3.rotr((g1d1 .^. g1a2: U32), 8n, 24n)
      +g1c2 = (g1c1 + g1d2: U32)
      +g1b2 = Blake3.rotr((g1b1 .^. g1c2: U32), 7n, 25n)
      +g2a1 = (s2 + s6 + m4: U32)
      +g2d1 = Blake3.rotr((s14 .^. g2a1: U32), 16n, 16n)
      +g2c1 = (s10 + g2d1: U32)
      +g2b1 = Blake3.rotr((s6 .^. g2c1: U32), 12n, 20n)
      +g2a2 = (g2a1 + g2b1 + m5: U32)
      +g2d2 = Blake3.rotr((g2d1 .^. g2a2: U32), 8n, 24n)
      +g2c2 = (g2c1 + g2d2: U32)
      +g2b2 = Blake3.rotr((g2b1 .^. g2c2: U32), 7n, 25n)
      +g3a1 = (s3 + s7 + m6: U32)
      +g3d1 = Blake3.rotr((s15 .^. g3a1: U32), 16n, 16n)
      +g3c1 = (s11 + g3d1: U32)
      +g3b1 = Blake3.rotr((s7 .^. g3c1: U32), 12n, 20n)
      +g3a2 = (g3a1 + g3b1 + m7: U32)
      +g3d2 = Blake3.rotr((g3d1 .^. g3a2: U32), 8n, 24n)
      +g3c2 = (g3c1 + g3d2: U32)
      +g3b2 = Blake3.rotr((g3b1 .^. g3c2: U32), 7n, 25n)
      +g4a1 = (g0a2 + g1b2 + m8: U32)
      +g4d1 = Blake3.rotr((g3d2 .^. g4a1: U32), 16n, 16n)
      +g4c1 = (g2c2 + g4d1: U32)
      +g4b1 = Blake3.rotr((g1b2 .^. g4c1: U32), 12n, 20n)
      +g4a2 = (g4a1 + g4b1 + m9: U32)
      +g4d2 = Blake3.rotr((g4d1 .^. g4a2: U32), 8n, 24n)
      +g4c2 = (g4c1 + g4d2: U32)
      g4b2 = Blake3.rotr((g4b1 .^. g4c2: U32), 7n, 25n)
      +g5a1 = (g1a2 + g2b2 + m10: U32)
      +g5d1 = Blake3.rotr((g0d2 .^. g5a1: U32), 16n, 16n)
      +g5c1 = (g3c2 + g5d1: U32)
      +g5b1 = Blake3.rotr((g2b2 .^. g5c1: U32), 12n, 20n)
      +g5a2 = (g5a1 + g5b1 + m11: U32)
      +g5d2 = Blake3.rotr((g5d1 .^. g5a2: U32), 8n, 24n)
      +g5c2 = (g5c1 + g5d2: U32)
      g5b2 = Blake3.rotr((g5b1 .^. g5c2: U32), 7n, 25n)
      +g6a1 = (g2a2 + g3b2 + m12: U32)
      +g6d1 = Blake3.rotr((g1d2 .^. g6a1: U32), 16n, 16n)
      +g6c1 = (g0c2 + g6d1: U32)
      +g6b1 = Blake3.rotr((g3b2 .^. g6c1: U32), 12n, 20n)
      +g6a2 = (g6a1 + g6b1 + m13: U32)
      +g6d2 = Blake3.rotr((g6d1 .^. g6a2: U32), 8n, 24n)
      +g6c2 = (g6c1 + g6d2: U32)
      g6b2 = Blake3.rotr((g6b1 .^. g6c2: U32), 7n, 25n)
      +g7a1 = (g3a2 + g0b2 + m14: U32)
      +g7d1 = Blake3.rotr((g2d2 .^. g7a1: U32), 16n, 16n)
      +g7c1 = (g1c2 + g7d1: U32)
      +g7b1 = Blake3.rotr((g0b2 .^. g7c1: U32), 12n, 20n)
      +g7a2 = (g7a1 + g7b1 + m15: U32)
      +g7d2 = Blake3.rotr((g7d1 .^. g7a2: U32), 8n, 24n)
      +g7c2 = (g7c1 + g7d2: U32)
      g7b2 = Blake3.rotr((g7b1 .^. g7c2: U32), 7n, 25n)
      St16{
        g4a2,
        g5a2,
        g6a2,
        g7a2,
        g7b2,
        g4b2,
        g5b2,
        g6b2,
        g6c2,
        g7c2,
        g4c2,
        g5c2,
        g5d2,
        g6d2,
        g7d2,
        g4d2
      }

# word i xor word i + 8, for the first eight words
def Blake3.fold(st: St16) -> Cv8:
  match st:
    case St16{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      Cv8{
        (s0 .^. s8: U32),
        (s1 .^. s9: U32),
        (s2 .^. s10: U32),
        (s3 .^. s11: U32),
        (s4 .^. s12: U32),
        (s5 .^. s13: U32),
        (s6 .^. s14: U32),
        (s7 .^. s15: U32)
      }

# The chaining value that compressing m into cv gives. The state is cv, the
# IV's first four words, the counter (high word 0), the block length and
# the flags; seven rounds, with the message permuted between them.
def Blake3.compress(cv: Cv8, m: Msg16, counter: U32, len: U32, flags: U32) -> Cv8:
  match cv:
    case Cv8{h0, h1, h2, h3, h4, h5, h6, h7}:
      st = {
        St16{
          h0,
          h1,
          h2,
          h3,
          h4,
          h5,
          h6,
          h7,
          1779033703,
          3144134277,
          1013904242,
          2773480762,
          counter,
          0,
          len,
          flags
        }: St16
      }
      +m1 = m
      +m2 = Blake3.permute(m1)
      +m3 = Blake3.permute(m2)
      +m4 = Blake3.permute(m3)
      +m5 = Blake3.permute(m4)
      +m6 = Blake3.permute(m5)
      m7 = Blake3.permute(m6)
      r1 = Blake3.round(st, m1)
      r2 = Blake3.round(r1, m2)
      r3 = Blake3.round(r2, m3)
      r4 = Blake3.round(r3, m4)
      r5 = Blake3.round(r4, m5)
      r6 = Blake3.round(r5, m6)
      r7 = Blake3.round(r6, m7)
      Blake3.fold(r7)

# the little-endian word of the bytes a, b, c and d
def Blake3.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  (a .|. (b << 8n) .|. (c << 16n) .|. (d << 24n): U32)

# the little-endian words of bs, four bytes each
def Blake3.words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Blake3.word(a, b, c, d) <> Blake3.words(t)
    case _:
      Nil{}

# the block of the sixteen words ws, or of zeros when ws is short
def Blake3.msg(ws: List<&2, U32>) -> Msg16:
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
                    Con{w8, Con{w9, Con{w10, Con{w11, Con{w12, Con{w13, Con{w14, Con{w15, _}}}}}}}}
                  }
                }
              }
            }
          }
        }
      }
    }:
      Msg16{w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15}
    case _:
      Msg16{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

# the block of the bytes cur, last first: its length, and its words with
# zeros up to 64 bytes
def Blake3.block(+cur: List<&2, U32>) -> Blk:
  +n = List.length(&2, U32, cur)
  pad = List.replicate(U32, Nat.sub(64n, n), 0)
  bs = List.append(&2, U32, List.reverse(&2, U32, cur), pad)
  Blk{U32.from_nat(n), Blake3.msg(Blake3.words(bs))}

# The blocks of the rest bs of the input, given cur, the bytes of the
# current block, last first; left, how many bytes it still takes; and acc,
# the finished blocks, last first. The empty input is one empty block.
def Blake3.blocks(
  bs: List<&2, U32>,
  cur: List<&2, U32>,
  left: Nat,
  acc: List<&2, Blk>
) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      match cur acc:
        case Nil{} Nil{}:
          [Blake3.block(Nil{})]
        case Nil{} _:
          List.reverse(&2, Blk, acc)
        case _ _:
          List.reverse(&2, Blk, Blake3.block(cur) <> acc)
    case Con{x, t}:
      match left:
        case 0n:
          Nil{}
        case 1n+p:
          match p:
            case 0n:
              Blake3.blocks(t, Nil{}, 64n, Blake3.block(x <> cur) <> acc)
            case 1n+q:
              Blake3.blocks(t, x <> cur, 1n+q, acc)

# the chunks of the rest bs of the blocks, sixteen blocks each, in the
# shape of Blake3.blocks
def Blake3.chunks(
  bs: List<&2, Blk>,
  cur: List<&2, Blk>,
  left: Nat,
  acc: List<&2, List<&2, Blk>>
) -> List<&2, List<&2, Blk>>:
  match bs:
    case Nil{}:
      match cur:
        case Nil{}:
          List.reverse(&2, List<&2, Blk>, acc)
        case _:
          List.reverse(&2, List<&2, Blk>, List.reverse(&2, Blk, cur) <> acc)
    case Con{x, t}:
      match left:
        case 0n:
          Nil{}
        case 1n+p:
          match p:
            case 0n:
              Blake3.chunks(t, Nil{}, 16n, List.reverse(&2, Blk, x <> cur) <> acc)
            case 1n+q:
              Blake3.chunks(t, x <> cur, 1n+q, acc)

# CHUNK_START (1) on the first block of a chunk, else no flag
def Blake3.start(first: Bool) -> U32:
  Bool.pick(U32, first, 1, 0)

# The pending last compression of a chunk at counter index: each block
# but the last compresses into the chaining value; the last one carries
# CHUNK_END (2).
def Blake3.chunk(bs: List<&2, Blk>, cv: Cv8, first: Bool, +index: U32) -> Pending:
  match bs:
    case Nil{}:
      Pending{cv, Blake3.msg(Nil{}), index, 0, 0}
    case Con{Blk{len, m}, Nil{}}:
      Pending{cv, m, index, len, (Blake3.start(first) .|. 2: U32)}
    case Con{Blk{len, m}, t}:
      Blake3.chunk(t, Blake3.compress(cv, m, index, len, Blake3.start(first)), False{}, index)

# the chaining value of a pending compression
def Blake3.value(p: Pending) -> Cv8:
  match p:
    case Pending{cv, block, counter, len, flags}:
      Blake3.compress(cv, block, counter, len, flags)

# the root output of a pending compression: the same, with ROOT (8)
def Blake3.root(p: Pending) -> Cv8:
  match p:
    case Pending{cv, block, counter, len, flags}:
      Blake3.compress(cv, block, counter, len, (flags .|. 8: U32))

# the pending compression of a parent: the IV as chaining value, the
# children's values as its block, counter 0, 64 bytes, PARENT (4)
def Blake3.parent(l: Cv8, r: Cv8) -> Pending:
  match l r:
    case Cv8{l0, l1, l2, l3, l4, l5, l6, l7} Cv8{r0, r1, r2, r3, r4, r5, r6, r7}:
      Pending{
        Blake3.iv(),
        Msg16{l0, l1, l2, l3, l4, l5, l6, l7, r0, r1, r2, r3, r4, r5, r6, r7},
        0,
        64,
        4
      }

# the largest power of two below n, for n of 2 or more: the high bit of n - 1
def Blake3.left(n: U32) -> U32:
  +x0 = (n - 1: U32)
  +x1 = (x0 .|. (x0 >> 1n): U32)
  +x2 = (x1 .|. (x1 >> 2n): U32)
  +x3 = (x2 .|. (x2 >> 4n): U32)
  +x4 = (x3 .|. (x3 >> 8n): U32)
  +x5 = (x4 .|. (x4 >> 16n): U32)
  (x5 .^. (x5 >> 1n): U32)

# The pending root compression of the n chunks cs, the first at counter
# index. The two subtrees run in parallel. depth bounds the recursion: the
# tree over 2^32 chunks is 33 levels deep.
def Blake3.tree(depth: Nat, cs: List<&2, List<&2, Blk>>, +n: U32, +index: U32) -> Pending:
  match depth:
    case 0n:
      Pending{Blake3.iv(), Blake3.msg(Nil{}), 0, 0, 0}
    case 1n+(+d):
      match cs:
        case Nil{}:
          Pending{Blake3.iv(), Blake3.msg(Nil{}), 0, 0, 0}
        case Con{c, Nil{}}:
          Blake3.chunk(c, Blake3.iv(), True{}, index)
        case Con{c, Con{e, r}}:
          +all = {Con{c, Con{e, r}}: List<&2, List<&2, Blk>>}
          +k = Blake3.left(n)
          ls = List.take(&2, List<&2, Blk>, all, U32.to_nat(k))
          rs = List.drop(&2, List<&2, Blk>, all, U32.to_nat(k))
          lp rp = Blake3.tree(d, ls, k, index) Blake3.tree(d, rs, (n - k: U32), (index + k: U32))
          Blake3.parent(Blake3.value(lp), Blake3.value(rp))

# the 32 bytes of a chaining value, little-endian
def Blake3.bytes(cv: Cv8) -> Octets.Bytes():
  match cv:
    case Cv8{+h0, +h1, +h2, +h3, +h4, +h5, +h6, +h7}:
      [
        (h0 .&. 255: U32),
        ((h0 >> 8n) .&. 255: U32),
        ((h0 >> 16n) .&. 255: U32),
        (h0 >> 24n: U32),
        (h1 .&. 255: U32),
        ((h1 >> 8n) .&. 255: U32),
        ((h1 >> 16n) .&. 255: U32),
        (h1 >> 24n: U32),
        (h2 .&. 255: U32),
        ((h2 >> 8n) .&. 255: U32),
        ((h2 >> 16n) .&. 255: U32),
        (h2 >> 24n: U32),
        (h3 .&. 255: U32),
        ((h3 >> 8n) .&. 255: U32),
        ((h3 >> 16n) .&. 255: U32),
        (h3 >> 24n: U32),
        (h4 .&. 255: U32),
        ((h4 >> 8n) .&. 255: U32),
        ((h4 >> 16n) .&. 255: U32),
        (h4 >> 24n: U32),
        (h5 .&. 255: U32),
        ((h5 >> 8n) .&. 255: U32),
        ((h5 >> 16n) .&. 255: U32),
        (h5 >> 24n: U32),
        (h6 .&. 255: U32),
        ((h6 >> 8n) .&. 255: U32),
        ((h6 >> 16n) .&. 255: U32),
        (h6 >> 24n: U32),
        (h7 .&. 255: U32),
        ((h7 >> 8n) .&. 255: U32),
        ((h7 >> 16n) .&. 255: U32),
        (h7 >> 24n: U32)
      ]

# BLAKE3's 32-byte hash of b, in its default hash mode (no key, no context
# string)
def Hash.blake3(b: Octets.Bytes()) -> Octets.Bytes():
  +cs = Blake3.chunks(Blake3.blocks(b, Nil{}, 64n, Nil{}), Nil{}, 16n, Nil{})
  n = U32.from_nat(List.length(&2, List<&2, Blk>, cs))
  Blake3.bytes(Blake3.root(Blake3.tree(40n, cs, n, 0)))

# the lowercase hex digit of x, for x below 16
def Hash.digit(+x: U32) -> Char:
  Bool.pick(Char, (x < 10: U32), Chr{(x + 48: U32)}, Chr{(x + 87: U32)})

# the lowercase hex of h: two digits per byte, high digit first
def Hash.hex(h: Octets.Bytes()) -> String:
  match h:
    case Nil{}:
      SNil{}
    case Con{+x, t}:
      SCon{Hash.digit((x >> 4n: U32)), SCon{Hash.digit((x .&. 15: U32)), Hash.hex(t)}}
