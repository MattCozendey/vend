import Base
import ../shared/shared/sha256/spec.bend as Sha256
import ../shared/shared/shared/shared.bend as Shared
import ../shared/signatures/spec.bend as Signatures

# A fact is what nodes share: words written by an author, and the author's
# signature of them. What the words mean is up to the hooks. A node holds its
# facts in a fact set: the patricia_map PatriciaMap(~Unit, ~(Shared.Row(U32, 8n)),
# ~FactSet.measure, ~FactSet.combine), a map from the key of each fact to
# nothing. A def cannot name that type while the map is still open laws, so the
# modules above write it out.

# a fact: its author's public key, its words, and the author's signature of
# its words
type Fact is Data:
  Fact{author: Shared.Row(U32, 8n), body: List<&2, U32>, signature: List<&2, U32>}

# the key of the fact f: the words that a fact set keeps for it
law Fact.key:
  for f: Fact
  List<&2, U32>

# the fact whose key is k, if k is the key of a fact
law Fact.from_key:
  for k: List<&2, U32>
  Maybe<&2, Fact>

# the signature of the fact f checks
law Fact.checks:
  for f: Fact
  Bool

# the measure of the entry of the key k in a fact set
law FactSet.measure:
  for k: List<&2, U32>
  for u: Unit
  Shared.Row(U32, 8n)

# the summaries x and y of two halves of a fact set, combined
law FactSet.combine:
  for x: Shared.Row(U32, 8n)
  for y: Shared.Row(U32, 8n)
  Shared.Row(U32, 8n)

# Means: the key of a fact reads back as that fact, and a key that reads back
# as a fact is that fact's key.
# For free: two facts with one key are the same fact, and one fact has one key,
# so a fact set holds each fact once and two nodes that hold the same facts
# hold the same set; a key is all that a node needs to send a fact, and all
# that the other node needs to read it.
# For the goal: Sync sends keys, and a node turns each key it receives into the
# fact or into nothing, never into another fact.
# Example: a vote of node a for slot 5 has one key; that key reads back as that
# vote, and words that are no key read as no fact.
law Fact.key_reads_back:
  for f: Fact
  for k: List<&2, U32>
  {
    Fact.from_key(Fact.key(f)) == Some{f}: Maybe<&2, Fact>
  }
    & ({Fact.from_key(k) == Some{f}: Maybe<&2, Fact>} -> {k == Fact.key(f): List<&2, U32>})

# Means: a fact checks exactly when its signature checks for its words with
# its author's public key.
# For free: a fact that nobody but its author could make checks only if its
# author made it (the signature assumption); a fact checks on every node alike.
# For the goal: a node keeps a fact only when it checks, so nothing that a
# stranger sends is kept unless its author signed it (Trust 3).
# Example: a vote whose signature is of other words does not check.
law Fact.checks_is_signature_check:
  for a: Shared.Row(U32, 8n)
  for b: List<&2, U32>
  for s: List<&2, U32>
  {Fact.checks(Fact{a, b, s}) == Signatures.Signature.checks(a, b, s): Bool}

# Means: the measure of an entry of a fact set is the SHA-256 of its key, and
# two summaries combine as the SHA-256 of their words, one after the other.
# For free: with the summary law of patricia_map, the summary of each part of
# a fact set is a Merkle hash of its facts; two parts with different facts
# have different summaries unless SHA-256 has a collision.
# For the goal: two nodes find the parts where their facts differ by comparing
# summaries, and trust nothing but SHA-256 to do it (Trust 1); a Sync costs
# what differs, not what the nodes hold.
# Example: two nodes with the same facts in a part have equal summaries of that
# part, so neither sends that part.
law FactSet.summaries_are_merkle_hashes:
  for k: List<&2, U32>
  for u: Unit
  for x: Shared.Row(U32, 8n)
  for y: Shared.Row(U32, 8n)
  {
    FactSet.measure(k, u) == Sha256.Sha256.of_words(k): Shared.Row(U32, 8n)
  }
    & {
      FactSet.combine(
        x,
        y
      )
        == Sha256.Sha256.of_words(
          List.append(&2, U32, Shared.Row.to_list(U32, 8n, x), Shared.Row.to_list(U32, 8n, y))
        ): Shared.Row(U32, 8n)
    }
