import Base
import ./shared/hash.bend as Hashes
import ./shared/shared.bend as Shared

# Depots
# ------
# A depot gives the words that it holds under a hash (fetch). A tree, a rope
# and a ledger's data are kept in one: each of their nodes is words under
# their hash. A depot only grows, so what it gives, it gives for good. A
# value is read from the words under its hash with Code.whole.of.

# the depot s holds the words ws, under their hash
def Depot.has(
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

# the depot s holds each of the words ns, under their hashes
def Depot.holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ns: List<&2, List<&2, U32>>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{ws, r}:
      List.all.if(u => Depot.holds(~S, ~fetch, s, r), Depot.has(~S, ~fetch, s, ws))

# that a depot b, which grows from a depot a (grows), gives the words that a
# gives
def Depot.Keeps(
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
