import Base
import ../shared.bend as Shared

# A view reads a resource's bytes as a document of its own type D, and
# writes the document back. ok tells the documents that the view can
# write: dec gives only those, and enc takes only those.

# enc then dec gives a valid document back
def View.ReadBack(
  ~D: Data,
  ~ok: D -> Bool,
  ~dec: Shared.Bytes() -> Maybe<&2, D>,
  ~enc: D -> Shared.Bytes()
) -> Type:
  @d: D -> {ok(d) == True{}: Bool} -> {dec(enc(d)) == Some{d}: Maybe<&2, D>}

# when dec accepts bytes, enc gives exactly those bytes back
def View.WriteBack(
  ~D: Data,
  ~ok: D -> Bool,
  ~dec: Shared.Bytes() -> Maybe<&2, D>,
  ~enc: D -> Shared.Bytes()
) -> Type:
  @b: Shared.Bytes() -> @d: D -> {dec(b) == Some{d}: Maybe<&2, D>} -> {enc(d) == b: Shared.Bytes()}

# dec gives only valid documents
def View.DecodesValid(
  ~D: Data,
  ~ok: D -> Bool,
  ~dec: Shared.Bytes() -> Maybe<&2, D>,
  ~enc: D -> Shared.Bytes()
) -> Type:
  @b: Shared.Bytes() -> @d: D -> {dec(b) == Some{d}: Maybe<&2, D>} -> {ok(d) == True{}: Bool}

# enc writes a valid document as real bytes
def View.EncodesBytes(
  ~D: Data,
  ~ok: D -> Bool,
  ~dec: Shared.Bytes() -> Maybe<&2, D>,
  ~enc: D -> Shared.Bytes()
) -> Type:
  @d: D -> {ok(d) == True{}: Bool} -> {Shared.is_bytes(enc(d)) == True{}: Bool}

# The contract of a view: it loses nothing. Together, the four parts say
# that the bytes dec accepts and the valid documents are one to one through
# enc, so each content has exactly one document.
def View.Lossless(
  ~D: Data,
  ~ok: D -> Bool,
  ~dec: Shared.Bytes() -> Maybe<&2, D>,
  ~enc: D -> Shared.Bytes()
) -> Type:
  View.ReadBack(~D, ~ok, ~dec, ~enc) &
    (
      View.WriteBack(
        ~D,
        ~ok,
        ~dec,
        ~enc
      )
        & (View.DecodesValid(~D, ~ok, ~dec, ~enc) & View.EncodesBytes(~D, ~ok, ~dec, ~enc))
    )

# Diff and patch
# --------------

# a patch of a with the diff from a to b gives b
def View.Patches(~D: Data, ~E: Data, ~diff: D -> D -> E, ~patch: D -> E -> Maybe<&2, D>) -> Type:
  @a: D -> @b: D -> {patch(a, diff(a, b)) == Some{b}: Maybe<&2, D>}

# the diff from a document to itself is empty
def View.DiffsNothing(~D: Data, ~E: Data, ~diff: D -> D -> E, ~is_empty: E -> Bool) -> Type:
  @a: D -> {is_empty(diff(a, a)) == True{}: Bool}

# Equivalence
# -----------
# A view decides which changes change meaning. The history keeps every
# version, but two documents that are the same to their view differ only in
# trivia, and nothing downstream reacts. Each view picks its own sense, so
# it must be a real equivalence: else many small "no change" steps could
# add up to a large change.

# every document is the same as itself
def View.Reflexive(~D: Data, ~same: D -> D -> Bool) -> Type:
  @a: D -> {same(a, a) == True{}: Bool}

# the order of a comparison does not matter
def View.Symmetric(~D: Data, ~same: D -> D -> Bool) -> Type:
  @a: D -> @b: D -> {same(a, b) == True{}: Bool} -> {same(b, a) == True{}: Bool}

# the same as the same is the same
def View.Transitive(~D: Data, ~same: D -> D -> Bool) -> Type:
  @a: D -> @b: D -> @c: D -> {
    same(a, b) == True{}: Bool
  } -> {same(b, c) == True{}: Bool} -> {same(a, c) == True{}: Bool}

# same is an equivalence
def View.Equivalence(~D: Data, ~same: D -> D -> Bool) -> Type:
  View.Reflexive(~D, ~same) & (View.Symmetric(~D, ~same) & View.Transitive(~D, ~same))

# Merge
# -----
# A three-way merge of two documents that both come from base. None is a
# clash that the view cannot settle; a caller keeps both sides then.

# a side that did not change takes the other side
def View.MergeKeeps(~D: Data, ~merge: D -> D -> D -> Maybe<&2, D>) -> Type:
  (@b: D -> @x: D -> {merge(b, b, x) == Some{x}: Maybe<&2, D>}) &
    (@b: D -> @x: D -> {merge(b, x, b) == Some{x}: Maybe<&2, D>})

# two sides with the same change merge to it
def View.MergeAgrees(~D: Data, ~merge: D -> D -> D -> Maybe<&2, D>) -> Type:
  @b: D -> @x: D -> {merge(b, x, x) == Some{x}: Maybe<&2, D>}

# the order of the sides does not matter
def View.MergeSymmetric(~D: Data, ~merge: D -> D -> D -> Maybe<&2, D>) -> Type:
  @b: D -> @x: D -> @y: D -> {merge(b, x, y) == merge(b, y, x): Maybe<&2, D>}

# merge is a three-way merge
def View.Merges(~D: Data, ~merge: D -> D -> D -> Maybe<&2, D>) -> Type:
  View.MergeKeeps(~D, ~merge) & (View.MergeAgrees(~D, ~merge) & View.MergeSymmetric(~D, ~merge))

# Items
# -----
# A view may name items in its documents (the defs of a Bend module, the
# macros of a C file). The graph selects items by key, so a change matters
# to an importer only when an item it selects changed.

# no key of ks comes twice
def Keys.distinct(ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{k, t}:
      +t = t
      List.all.if(u => Keys.distinct(t), Bool.not(List.contains(~String, ~String.eq, t, k)))

# a key names one item: the keys of every document are distinct
def View.KeysDistinct(~D: Data, ~keys: D -> List<&2, String>) -> Type:
  @d: D -> {Keys.distinct(keys(d)) == True{}: Bool}

# Obligations and verifiers
# -------------------------
# A view may say what a resource still owes (its open obligations) and
# name an outside program that checks a resource in a folder (its
# verifier). The core never names a kind of obligation, nor a program: it
# only lists what the views give.

# An open obligation: kind, a word its view defines; item, the key of the
# item it is about; text, what is open there.
type Obligation is Data:
  Obligation{kind: String, item: String, text: String}

# a and b are the same obligation
def Obligation.is_eq(a: Obligation, b: Obligation) -> Bool:
  match a b:
    case Obligation{k1, i1, t1} Obligation{k2, i2, t2}:
      List.all.if(u => List.all.if(v => String.eq(t1, t2), String.eq(i1, i2)), String.eq(k1, k2))

# An outside check of a resource: run program with the arguments before,
# then the resource's file path, then the arguments after; its output is
# the verdict.
type Verifier is Data:
  Verifier{program: String, before: List<&2, String>, after: List<&2, String>}

# Sequence diff and merge
# -----------------------
# The views diff and merge sequences (the lines of a text, the items of a
# Bend module) the same way. A diff trims the common start and end, then
# aligns the two middles by a longest common subsequence (dynamic
# programming: time and memory grow with the product of the two middles'
# lengths), and reads the changes off as hunks in the old sequence's
# coordinates. A three-way merge applies the hunks of both sides to the
# base when no two of them collide; two hunks collide when they start at
# one place or their old ranges overlap. Equal hunks are taken once, and
# resolve, given the base, may settle a collision of two different ones.

# One change, in the coordinates of the old sequence: replace del items
# from start with ins.
type Hunk<-T: Data> is Data:
  Hunk{start: Nat, del: Nat, ins: List<&2, T>}

# One step of an alignment: keep the next old item, drop it, or add x.
type Op<-T: Data> is Data:
  OpKeep{}
  OpDrop{}
  OpAdd{x: T}

# The hunk being read off an alignment: none, or one from start with del
# dropped items and its added items, last first.
type Open<-T: Data> is Data:
  Shut{}
  Opened{start: Nat, del: Nat, rev: List<&2, T>}

# the first number of ns, or 0
def Seq.hd(ns: List<&2, Nat>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{n, t}:
      n

# the first row of rows, or no row
def Seq.top(rows: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      r

# every row of rows without its first number
def Seq.tails(rows: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.tail(&2, Nat, r) <> Seq.tails(t)

# how many items xs and ys share at their start
def Seq.common(~T: Data, ~eq: T -> T -> Bool, xs: List<&2, T>, ys: List<&2, T>) -> Nat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Shared.Bool.when(Nat, eq(x, y), u => 1n+Seq.common(~T, ~eq, xt, yt), u => 0n)
    case _ _:
      0n

# n zeros
def Seq.zeros(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> Seq.zeros(p)

# the row of the table for old item a, against bs: entry j is the length of
# a longest common subsequence of a's suffix and bs's suffix from j; next
# is the row of the old item after a, from the same j
def Seq.row(
  ~T: Data,
  ~eq: T -> T -> Bool,
  +a: T,
  bs: List<&2, T>,
  next: List<&2, Nat>
) -> List<&2, Nat>:
  match bs next:
    case Con{b, bt} Con{n0, nt}:
      +nt = nt
      +rest = Seq.row(~T, ~eq, a, bt, nt)
      here = Shared.Bool.when(Nat, eq(a, b), u => 1n+Seq.hd(nt), u => Nat.max(n0, Seq.hd(rest)))
      here <> rest
    case _ _:
      [0n]

# the rows of the table, one per old item and one for the end
def Seq.rows(
  ~T: Data,
  ~eq: T -> T -> Bool,
  xs: List<&2, T>,
  +bs: List<&2, T>
) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      [Seq.zeros(1n+List.length(&2, T, bs))]
    case Con{x, t}:
      +next = Seq.rows(~T, ~eq, t, bs)
      Seq.row(~T, ~eq, x, bs, Seq.top(next)) <> next

# every item of bs as added
def Seq.adds(~T: Data, bs: List<&2, T>) -> List<&2, Op<T>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      OpAdd{b} <> Seq.adds(~T, t)

# every item of xs as dropped
def Seq.drops(~T: Data, xs: List<&2, T>) -> List<&2, Op<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      OpDrop{} <> Seq.drops(~T, t)

# an alignment of xs to ys along the table rows: keep equal items; else
# drop the old item when that loses no common item, or add the new one
def Seq.trace(
  ~T: Data,
  ~eq: T -> T -> Bool,
  +xs: List<&2, T>,
  +ys: List<&2, T>,
  +rows: List<&2, List<&2, Nat>>
) -> List<&2, Op<T>>:
  match xs ys:
    case Nil{} _:
      Seq.adds(~T, ys)
    case _ Nil{}:
      Seq.drops(~T, xs)
    case Con{x, xt} Con{y, yt}:
      down = Seq.hd(Seq.top(List.tail(&2, List<&2, Nat>, rows)))
      right = Seq.hd(List.tail(&2, Nat, Seq.top(rows)))
      Shared.Bool.when(
        List<&2, Op<T>>,
        eq(x, y),
        u => OpKeep{} <> Seq.trace(~T, ~eq, xt, yt, Seq.tails(List.tail(&2, List<&2, Nat>, rows))),
        u => Shared.Bool.when(
          List<&2, Op<T>>,
          Nat.is_le(right, down),
          v => OpDrop{} <> Seq.trace(~T, ~eq, xt, ys, List.tail(&2, List<&2, Nat>, rows)),
          v => OpAdd{y} <> Seq.trace(~T, ~eq, xs, yt, Seq.tails(rows))
        )
      )

# the hunk of o, if one is open
def Seq.flush(~T: Data, o: Open<T>) -> List<&2, Hunk<T>>:
  match o:
    case Shut{}:
      Nil{}
    case Opened{s, d, rev}:
      [Hunk{s, d, List.reverse(&2, T, rev)}]

# the hunks of an alignment; pos is the old position, o the hunk being read
def Seq.hunks(~T: Data, ops: List<&2, Op<T>>, +pos: Nat, o: Open<T>) -> List<&2, Hunk<T>>:
  match ops o:
    case Nil{} _:
      Seq.flush(~T, o)
    case Con{OpKeep{}, t} _:
      List.append(&2, Hunk<T>, Seq.flush(~T, o), Seq.hunks(~T, t, 1n+pos, Shut{}))
    case Con{OpDrop{}, t} Shut{}:
      Seq.hunks(~T, t, 1n+pos, Opened{pos, 1n, Nil{}})
    case Con{OpDrop{}, t} Opened{s, d, rev}:
      Seq.hunks(~T, t, 1n+pos, Opened{s, 1n+d, rev})
    case Con{OpAdd{x}, t} Shut{}:
      Seq.hunks(~T, t, pos, Opened{pos, 0n, [x]})
    case Con{OpAdd{x}, t} Opened{s, d, rev}:
      Seq.hunks(~T, t, pos, Opened{s, d, x <> rev})

# the hunks that turn xs into ys, in xs's coordinates, in order
def Seq.diff(~T: Data, ~eq: T -> T -> Bool, xs: List<&2, T>, ys: List<&2, T>) -> List<&2, Hunk<T>>:
  +xs = xs
  +ys = ys
  +p = Seq.common(~T, ~eq, xs, ys)
  +nx = List.length(&2, T, xs)
  +ny = List.length(&2, T, ys)
  room = Nat.sub(Nat.min(nx, ny), p)
  +s = Nat.min(Seq.common(~T, ~eq, List.reverse(&2, T, xs), List.reverse(&2, T, ys)), room)
  +mx = List.take(&2, T, List.drop(&2, T, xs, p), Nat.sub(Nat.sub(nx, p), s))
  +my = List.take(&2, T, List.drop(&2, T, ys, p), Nat.sub(Nat.sub(ny, p), s))
  Seq.hunks(~T, Seq.trace(~T, ~eq, mx, my, Seq.rows(~T, ~eq, mx, my)), p, Shut{})

# ins before the items of m, if m has any
def Seq.prepend(~T: Data, ins: List<&2, T>, m: Maybe<&2, List<&2, T>>) -> Maybe<&2, List<&2, T>>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{List.append(&2, T, ins, r)}

# xs from position pos after the hunks, which start at pos or later in
# order; None when a hunk does not fit
def Seq.apply(
  ~T: Data,
  +hs: List<&2, Hunk<T>>,
  +xs: List<&2, T>,
  +pos: Nat
) -> Maybe<&2, List<&2, T>>:
  match hs xs:
    case Nil{} _:
      Some{xs}
    case Con{Hunk{s, d, ins}, t} Nil{}:
      s = s
      d = d
      Shared.Bool.when(
        Maybe<&2, List<&2, T>>,
        Bool.and(Nat.is_eq(pos, s), Nat.is_eq(d, 0n)),
        u => Seq.prepend(~T, ins, Seq.apply(~T, t, Nil{}, pos)),
        u => None{}
      )
    case Con{Hunk{s, d, ins}, t} Con{x, xt}:
      +s = s
      +d = d
      Shared.Bool.when(
        Maybe<&2, List<&2, T>>,
        Nat.is_lt(pos, s),
        u => Seq.prepend(~T, [x], Seq.apply(~T, hs, xt, 1n+pos)),
        u => Shared.Bool.when(
          Maybe<&2, List<&2, T>>,
          Bool.and(Nat.is_eq(pos, s), Nat.is_le(d, List.length(&2, T, xs))),
          v => Seq.prepend(~T, ins, Seq.apply(~T, t, List.drop(&2, T, xs, d), Nat.add(pos, d))),
          v => None{}
        )
      )

# the hunks as steps to take in order: each start counts in the items as
# the steps before it left them; added and removed count what they did
def Seq.steps(~T: Data, hs: List<&2, Hunk<T>>, +added: Nat, +removed: Nat) -> List<&2, Hunk<T>>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Hunk{s, +d, +ins}, t}:
      n = List.length(&2, T, ins)
      Hunk{
        Nat.sub(Nat.add(s, added), removed),
        d,
        ins
      }
        <> Seq.steps(~T, t, Nat.add(added, n), Nat.add(removed, d))

# xs with del items at pos replaced by ins, or None when they are not there
def Seq.splice(
  ~T: Data,
  +xs: List<&2, T>,
  +pos: Nat,
  +del: Nat,
  ins: List<&2, T>
) -> Maybe<&2, List<&2, T>>:
  Shared.Bool.when(
    Maybe<&2, List<&2, T>>,
    Nat.is_le(Nat.add(pos, del), List.length(&2, T, xs)),
    u => Some{
      List.append(
        &2,
        T,
        List.take(&2, T, xs, pos),
        List.append(&2, T, ins, List.drop(&2, T, xs, Nat.add(pos, del)))
      )
    },
    u => None{}
  )

# m after each step in order, or None when one does not fit
def Seq.patch(~T: Data, hs: List<&2, Hunk<T>>, m: Maybe<&2, List<&2, T>>) -> Maybe<&2, List<&2, T>>:
  match hs m:
    case Nil{} _:
      m
    case Con{h, t} None{}:
      None{}
    case Con{Hunk{s, d, ins}, t} Some{xs}:
      Seq.patch(~T, t, Seq.splice(~T, xs, s, d, ins))

# xs and ys are the same items
def Seq.is_eq(~T: Data, ~eq: T -> T -> Bool, xs: List<&2, T>, ys: List<&2, T>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Seq.is_eq(~T, ~eq, xt, yt), eq(x, y))
    case _ _:
      False{}

# a and b are the same hunk
def Hunk.is_eq(~T: Data, ~eq: T -> T -> Bool, a: Hunk<T>, b: Hunk<T>) -> Bool:
  match a b:
    case Hunk{s1, d1, i1} Hunk{s2, d2, i2}:
      List.all.if(u => Seq.is_eq(~T, ~eq, i1, i2), Bool.and(Nat.is_eq(s1, s2), Nat.is_eq(d1, d2)))

# where the old range of h starts
def Hunk.start(~T: Data, h: Hunk<T>) -> Nat:
  match h:
    case Hunk{s, d, i}:
      s

# where the old range of h ends
def Hunk.end(~T: Data, h: Hunk<T>) -> Nat:
  match h:
    case Hunk{s, d, i}:
      Nat.add(s, d)

# a and b collide: they start at one place, or their old ranges overlap (an
# insertion collides with a range it falls strictly inside)
def Hunk.collide(~T: Data, +a: Hunk<T>, +b: Hunk<T>) -> Bool:
  +s1 = Hunk.start(~T, a)
  +s2 = Hunk.start(~T, b)
  overlap = Bool.and(Nat.is_lt(s1, Hunk.end(~T, b)), Nat.is_lt(s2, Hunk.end(~T, a)))
  Bool.or(Nat.is_eq(s1, s2), overlap)

# h after the hunks merged so far, which end at last: None when h starts
# before that end
def Seq.take(
  ~T: Data,
  +h: Hunk<T>,
  last: Nat,
  k: Nat -> Maybe<&2, List<&2, Hunk<T>>>
) -> Maybe<&2, List<&2, Hunk<T>>>:
  Shared.Bool.when(
    Maybe<&2, List<&2, Hunk<T>>>,
    Nat.is_le(last, Hunk.start(~T, h)),
    u => Seq.prepend(~Hunk<T>, [h], k(Hunk.end(~T, h))),
    u => None{}
  )

# a settled collision, then the rest
def Seq.settled(
  ~T: Data,
  r: Maybe<&2, Hunk<T>>,
  last: Nat,
  k: Nat -> Maybe<&2, List<&2, Hunk<T>>>
) -> Maybe<&2, List<&2, Hunk<T>>>:
  match r:
    case None{}:
      None{}
    case Some{h}:
      Seq.take(~T, h, last, k)

# the merge of the two sides' hunk lists, from one base, after hunks that
# end at last; None on a collision that is neither equal nor resolved
def Seq.merge3(
  ~T: Data,
  ~eq: T -> T -> Bool,
  ~resolve: List<&2, T> -> Hunk<T> -> Hunk<T> -> Maybe<&2, Hunk<T>>,
  +base: List<&2, T>,
  +hx: List<&2, Hunk<T>>,
  +hy: List<&2, Hunk<T>>,
  +last: Nat
) -> Maybe<&2, List<&2, Hunk<T>>>:
  match hx hy:
    case Nil{} Nil{}:
      Some{Nil{}}
    case Nil{} Con{h, t}:
      Seq.take(~T, h, last, e => Seq.merge3(~T, ~eq, ~resolve, base, Nil{}, t, e))
    case Con{h, t} Nil{}:
      Seq.take(~T, h, last, e => Seq.merge3(~T, ~eq, ~resolve, base, t, Nil{}, e))
    case Con{+a, at} Con{+b, bt}:
      Shared.Bool.when(
        Maybe<&2, List<&2, Hunk<T>>>,
        Hunk.collide(~T, a, b),
        u => Shared.Bool.when(
          Maybe<&2, List<&2, Hunk<T>>>,
          Hunk.is_eq(~T, ~eq, a, b),
          v => Seq.take(~T, a, last, e => Seq.merge3(~T, ~eq, ~resolve, base, at, bt, e)),
          v => Seq.settled(
            ~T,
            resolve(base, a, b),
            last,
            e => Seq.merge3(~T, ~eq, ~resolve, base, at, bt, e)
          )
        ),
        u => Shared.Bool.when(
          Maybe<&2, List<&2, Hunk<T>>>,
          Nat.is_lt(Hunk.start(~T, a), Hunk.start(~T, b)),
          v => Seq.take(~T, a, last, e => Seq.merge3(~T, ~eq, ~resolve, base, at, hy, e)),
          v => Seq.take(~T, b, last, e => Seq.merge3(~T, ~eq, ~resolve, base, hx, bt, e))
        )
      )

# base after the merged hunks, if the merge settled
def Seq.merged(
  ~T: Data,
  m: Maybe<&2, List<&2, Hunk<T>>>,
  base: List<&2, T>
) -> Maybe<&2, List<&2, T>>:
  match m:
    case None{}:
      None{}
    case Some{hs}:
      Seq.apply(~T, hs, base, 0n)

# the three-way merge of x and y from base: both sides' changes applied to
# base, or None when they collide and resolve does not settle it
def Seq.merge(
  ~T: Data,
  ~eq: T -> T -> Bool,
  ~resolve: List<&2, T> -> Hunk<T> -> Hunk<T> -> Maybe<&2, Hunk<T>>,
  base: List<&2, T>,
  x: List<&2, T>,
  y: List<&2, T>
) -> Maybe<&2, List<&2, T>>:
  +base = base
  hx = Seq.diff(~T, ~eq, base, x)
  hy = Seq.diff(~T, ~eq, base, y)
  Seq.merged(~T, Seq.merge3(~T, ~eq, ~resolve, base, hx, hy, 0n), base)
