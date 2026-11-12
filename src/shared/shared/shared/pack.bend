import Base

# Packed bytes
# ------------
# Content is kept packed: a word holds four bytes, the first one highest, so
# a byte costs a quarter of a word, not a whole one. A piece of content is its
# length in bytes, then its words; the last word is filled with zeros. So
# packed pieces, one after the other, read back without a mark between them.

# the word of the bytes a, b, c and d
def Pack.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(a, 256), b), 256), c), 256), d)

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
  U32.from_nat(List.length(&2, U32, bs)) <> Pack.words(bs)

# each of the pieces ps, packed
def Pack.pieces(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      []
    case Con{x, rest}:
      Pack.piece(x) <> Pack.pieces(rest)

# the fourth byte of w, when a piece has one more byte to take, then rest
def Pack.byte.d(n: Nat, w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      U32.mod(w, 256) <> rest

# the third byte of w, and the fourth, as n says, then rest
def Pack.byte.c(n: Nat, +w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      U32.mod(U32.div(w, 256), 256) <> Pack.byte.d(p, w, rest)

# the second byte of w, and those after it, as n says, then rest
def Pack.byte.b(n: Nat, +w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      U32.mod(U32.div(w, 65536), 256) <> Pack.byte.c(p, w, rest)

# the first n bytes of the word w (four at most), then rest
def Pack.bytes(n: Nat, +w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      U32.div(w, 16777216) <> Pack.byte.b(p, w, rest)

# the bytes of the packed pieces ws, when left bytes of the piece that is
# being read are still to come (0: the next word is the length of a piece)
def Pack.read(ws: List<&2, U32>, left: Nat) -> List<&2, U32>:
  match ws left:
    case Nil{} n:
      []
    case Con{w, rest} 0n:
      Pack.read(rest, U32.to_nat(w))
    case Con{w, rest} 1n+(+p):
      Pack.bytes(1n+p, w, Pack.read(rest, Nat.sub(1n+p, 4n)))

# every element of bs is a byte
def Pack.fits(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      List.all.if(u => Pack.fits(rest), U32.is_lt(b, 256))

# every element of each of the pieces ps is a byte
def Pack.all_fit(ps: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{x, rest}:
      List.all.if(u => Pack.all_fit(rest), Pack.fits(x))

# the four bytes of each of the words ws: words as bytes
def Pack.unpack(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{+w, rest}:
      Pack.bytes(4n, w, Pack.unpack(rest))

# packed pieces read back as their bytes, one piece after the other
law Pack.read_pieces:
  for ps: List<&2, List<&2, U32>>
  {Pack.all_fit(ps) == True{}: Bool}
    -> {
      Pack.read(List.concat(&2, U32, Pack.pieces(ps)), 0n) == List.concat(&2, U32, ps): List<&2, U32>
    }

# words as bytes pack back to the words
law Pack.words_unpack:
  for ws: List<&2, U32>
  {Pack.words(Pack.unpack(ws)) == ws: List<&2, U32>}
