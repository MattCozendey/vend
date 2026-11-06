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
