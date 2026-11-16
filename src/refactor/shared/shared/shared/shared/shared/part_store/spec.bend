import Base
import ../shared/sha256/spec.bend as Sha256
import ../shared/shared/shared.bend as Shared
import ../shared/word_list_sets/spec.bend as WordListSets

# A part store holds parts of content, each under its SHA-256. Every part it
# holds is the words of its hash, so a part from anyone can be taken in: its
# hash checks it. A node keeps the parts that it needs and the parts that it
# signed a claim to keep; it may drop any other part only once enough trusted
# keepers, other than itself, signed claims to keep it. A node that lacks a
# part asks a peer for it by hash.

# a store of parts
law PartStore:
  Data

# the store with no part
law PartStore.empty:
  PartStore

# the store s with the part ws, under its hash
law PartStore.put:
  for s: PartStore
  for ws: List<&2, U32>
  PartStore

# the part of the hash h in s, if s holds one
law PartStore.get:
  for s: PartStore
  for h: Shared.FixedLengthList(U32, 8n)
  Maybe<&2, List<&2, U32>>

# the hashes of the parts of s
law PartStore.hashes:
  for s: PartStore
  List<&2, Shared.FixedLengthList(U32, 8n)>

# Keep claims
# -----------

# a signed claim of the node keeper that it keeps the part of the hash part
type KeepClaim is Data:
  KeepClaim{keeper: List<&2, U32>, part: Shared.FixedLengthList(U32, 8n)}

# the hashes a and b are the same
def same_hash(a: Shared.FixedLengthList(U32, 8n), b: Shared.FixedLengthList(U32, 8n)) -> Bool:
  WordListSets.same(
    Shared.FixedLengthList.to_list(U32, 8n, a),
    Shared.FixedLengthList.to_list(U32, 8n, b)
  )

# the keepers of the claims cs for the hash h
def claimers(
  cs: List<&2, KeepClaim>,
  +h: Shared.FixedLengthList(U32, 8n)
) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      []
    case Con{KeepClaim{k, p}, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, same_hash(p, h), [k], []),
        claimers(rest, h)
      )

# the keepers of ks other than me
def others(ks: List<&2, List<&2, U32>>, +me: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ks:
    case Nil{}:
      []
    case Con{+k, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, WordListSets.same(k, me), [], [k]),
        others(rest, me)
      )

# the keepers of ks that are trusted keepers (of keepers)
def trusted(
  ks: List<&2, List<&2, U32>>,
  +keepers: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match ks:
    case Nil{}:
      []
    case Con{+k, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(List<&2, List<&2, U32>>, WordListSets.contains(keepers, k), [k], []),
        trusted(rest, keepers)
      )

# no hash is twice in hs
def DistinctHashes(hs: List<&2, Shared.FixedLengthList(U32, 8n)>) -> Type:
  match hs:
    case Nil{}:
      Unit
    case Con{x, rest}:
      {has_hash(rest, x) == False{}: Bool} & DistinctHashes(rest)

# the node me may drop the part of the hash h: at least copies trusted keepers
# (of keepers), other than me, signed claims (among cs) to keep it
def may_drop(
  cs: List<&2, KeepClaim>,
  keepers: List<&2, List<&2, U32>>,
  copies: Nat,
  me: List<&2, U32>,
  h: Shared.FixedLengthList(U32, 8n)
) -> Bool:
  Nat.is_le(
    copies,
    List.length(
      &2,
      List<&2, U32>,
      WordListSets.dedupe(others(trusted(claimers(cs, h), keepers), me))
    )
  )

# the node me claimed, among cs, to keep the part of the hash h
def claimed_by(
  cs: List<&2, KeepClaim>,
  me: List<&2, U32>,
  h: Shared.FixedLengthList(U32, 8n)
) -> Bool:
  WordListSets.contains(claimers(cs, h), me)

# found, or the hash h is one of hs
def has_hash.go(
  hs: List<&2, Shared.FixedLengthList(U32, 8n)>,
  +h: Shared.FixedLengthList(U32, 8n),
  found: Bool
) -> Bool:
  match hs:
    case Nil{}:
      found
    case Con{x, rest}:
      match found:
        case True{}:
          True{}
        case False{}:
          has_hash.go(rest, h, same_hash(x, h))

# the hash h is one of hs
def has_hash(
  hs: List<&2, Shared.FixedLengthList(U32, 8n)>,
  h: Shared.FixedLengthList(U32, 8n)
) -> Bool:
  has_hash.go(hs, h, False{})

# the store s after the node me drops parts: it keeps every part of needed,
# every part that it claimed among cs, and every part that it may not drop
law PartStore.drop:
  for s: PartStore
  for cs: List<&2, KeepClaim>
  for keepers: List<&2, List<&2, U32>>
  for copies: Nat
  for me: List<&2, U32>
  for needed: List<&2, Shared.FixedLengthList(U32, 8n)>
  PartStore

# Fetching
# --------

# the message that asks a peer for the parts of the hashes hs
law PartFetch.ask:
  for hs: List<&2, Shared.FixedLengthList(U32, 8n)>
  List<&2, U32>

# the answer of a node with the store s to the message m: the parts that m asks
# for and s holds
law PartFetch.answer:
  for s: PartStore
  for m: List<&2, U32>
  List<&2, U32>

# the store s after it takes in the answer m
law PartFetch.take:
  for s: PartStore
  for m: List<&2, U32>
  PartStore

# Laws
# ----

# Means: every part that a store holds is the words of its hash.
# For free: a part from any node, honest or not, is right or absent, never
# wrong; content is stored once by hash, however many versions share it.
# For the goal: a node fetches a part from anyone and trusts only SHA-256
# (Trust 1); content is stored once (Cost 1).
# Example: a store that holds a part under the hash H gives words whose SHA-256
# is H.
law PartStore.part_is_its_hash:
  for s: PartStore
  for h: Shared.FixedLengthList(U32, 8n)
  for ws: List<&2, U32>
  {
    PartStore.get(s, h) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {Sha256.Sha256.of_words(ws) == h: Shared.FixedLengthList(U32, 8n)}

# Means: the empty store holds no part.
# For free: a new node starts with no content and fetches what it needs.
# For the goal: every store starts from nothing, so everything it holds came
# through put or a fetch, and checks.
# Example: the empty store has nothing under any hash.
law PartStore.empty_holds_nothing:
  for h: Shared.FixedLengthList(U32, 8n)
  {PartStore.get(PartStore.empty, h) == None{}: Maybe<&2, List<&2, U32>>}

# Means: putting a part adds it under its hash, unless the store already holds
# a part under that hash, and changes nothing else.
# For free: putting the same part twice is putting it once; the other parts
# stay as they were.
# For the goal: a write, a mount or a fetch stores its content once (Cost 1).
# Example: putting "hi" into an empty store holds "hi" under SHA-256("hi").
law PartStore.get_after_put:
  for s: PartStore
  for ws: List<&2, U32>
  for h: Shared.FixedLengthList(U32, 8n)
  {
    PartStore.get(
      PartStore.put(s, ws),
      h
    )
      == Maybe.or(
        &2,
        List<&2, U32>,
        PartStore.get(s, h),
        Bool.pick(
          Maybe<&2, List<&2, U32>>,
          same_hash(h, Sha256.Sha256.of_words(ws)),
          Some{ws},
          None{}
        )
      ): Maybe<&2, List<&2, U32>>
  }

# Means: the hashes of a store are exactly the hashes it holds a part for, each
# once.
# For free: a node can say which parts it holds, and claim or offer them.
# For the goal: keep claims and fetches name parts by these hashes.
# Example: a store with "hi" and "ho" lists two hashes.
law PartStore.hashes_are_held:
  for s: PartStore
  for h: Shared.FixedLengthList(U32, 8n)
  {
    has_hash(PartStore.hashes(s), h) == Maybe.is_some(&2, List<&2, U32>, PartStore.get(s, h)): Bool
  }
    & DistinctHashes(PartStore.hashes(s))

# Means: dropping never adds or changes a part; it keeps every part that the
# node needs or claimed; and it drops a part only when at least copies trusted
# keepers, other than the node, signed claims to keep it.
# For free: a part is never lost by a drop while fewer than copies keepers
# promised it; an honest keeper never drops what it claimed, so a dropped part
# stays with at least copies keepers that promised it.
# For the goal: every part is kept by enough nodes to never be lost, and each
# node keeps only the part it uses (Behavior 3, Store).
# Example: with copies 2, a node drops a part only after two other keepers
# signed that they keep it.
law PartStore.drop_is_safe:
  for s: PartStore
  for cs: List<&2, KeepClaim>
  for keepers: List<&2, List<&2, U32>>
  for copies: Nat
  for me: List<&2, U32>
  for needed: List<&2, Shared.FixedLengthList(U32, 8n)>
  for h: Shared.FixedLengthList(U32, 8n)
  for ws: List<&2, U32>
  (
    {
      PartStore.get(
        PartStore.drop(s, cs, keepers, copies, me, needed),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    } -> {PartStore.get(s, h) == Some{ws}: Maybe<&2, List<&2, U32>>}
  )
    & (
      {
        Bool.or(has_hash(needed, h), claimed_by(cs, me, h)) == True{}: Bool
      } -> {
        PartStore.get(
          PartStore.drop(s, cs, keepers, copies, me, needed),
          h
        )
          == PartStore.get(s, h): Maybe<&2, List<&2, U32>>
      }
    )
    & (
      {
        Maybe.is_some(&2, List<&2, U32>, PartStore.get(s, h)) == True{}: Bool
      } -> {
        Maybe.is_none(
          &2,
          List<&2, U32>,
          PartStore.get(PartStore.drop(s, cs, keepers, copies, me, needed), h)
        )
          == True{}: Bool
      } -> {may_drop(cs, keepers, copies, me, h) == True{}: Bool}
    )

# Means: taking in a peer's answer to an ask gives every asked part that the
# peer holds.
# For free: a node gets any part from any node that holds it; a wrong part from
# a faulty peer is never kept (the law above it).
# For the goal: a store is held by many nodes, each keeping the part it uses
# and fetching the rest on demand (Store).
# Example: a node asks a peer for H; the peer holds "hi" under H; after taking
# the answer, the node holds "hi" under H.
law PartFetch.fetch_gets:
  for s: PartStore
  for t: PartStore
  for hs: List<&2, Shared.FixedLengthList(U32, 8n)>
  for h: Shared.FixedLengthList(U32, 8n)
  {has_hash(hs, h) == True{}: Bool}
    -> {Maybe.is_some(&2, List<&2, U32>, PartStore.get(t, h)) == True{}: Bool}
    -> {
      Maybe.is_some(
        &2,
        List<&2, U32>,
        PartStore.get(PartFetch.take(s, PartFetch.answer(t, PartFetch.ask(hs))), h)
      )
        == True{}: Bool
    }

# Means: taking in any message never loses a part.
# For free: a faulty peer's message can only add parts, and those check.
# For the goal: nothing that a peer sends can make a node lose content.
# Example: a garbage message leaves the store as it was or with more parts.
law PartFetch.take_keeps:
  for s: PartStore
  for m: List<&2, U32>
  for h: Shared.FixedLengthList(U32, 8n)
  for ws: List<&2, U32>
  {
    PartStore.get(s, h) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {PartStore.get(PartFetch.take(s, m), h) == Some{ws}: Maybe<&2, List<&2, U32>>}
