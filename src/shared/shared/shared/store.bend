import Base
import ./shared/hash.bend as Hashes
import ./shared/shared.bend as Shared

# Stores
# ------
# A store gives the words that it holds under a hash (fetch). A tree, a rope
# and a ledger's data are kept in one: each of their nodes is words under
# their hash. A store only grows, so what it gives, it gives for good.

# the store s holds the words ws, under their hash
def Store.has(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +ws: List<&2, U32>
) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    fetch(s)(Hashes.Sha.hash(ws)),
    Some{ws}
  )

# the store s holds each of the words ns, under their hashes
def Store.holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ns: List<&2, List<&2, U32>>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{ws, r}:
      List.all.if(u => Store.holds(~S, ~fetch, s, r), Store.has(~S, ~fetch, s, ws))

# that a store b, which grows from a store a (grows), gives the words that a
# gives
def Store.Keeps(
  -S: Data,
  fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  grows: S -> S -> Bool
) -> Type:
  @a: S -> @b: S -> @h: Hashes.Hash -> @w: List<
    &2,
    U32> -> {
    grows(a, b) == True{}: Bool
  } -> {
    fetch(a)(h) == Some{w}: Maybe<&2, List<&2, U32>>
  } -> {fetch(b)(h) == Some{w}: Maybe<&2, List<&2, U32>>}
