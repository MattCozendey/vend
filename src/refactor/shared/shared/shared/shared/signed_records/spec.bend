import Base
import ../shared/patricia_map/spec.bend as PatriciaMap
import ../shared/shared/sha256/spec.bend as Sha256
import ../shared/shared/shared/shared.bend as Shared
import ../shared/signatures/spec.bend as Signatures

# A record is what nodes share: words written by an author, and the author's
# signature of them. What the words mean is up to the hooks. A node holds its
# records in a record set (SignedRecordSet).

# a record: its author's public key, its words, and the author's signature of
# its words
type SignedRecord is Data:
  SignedRecord{
    author: Shared.FixedLengthList(U32, 8n),
    body: List<&2, U32>,
    signature: List<&2, U32>
  }

# the key of the record f: the words that a record set keeps for it
law SignedRecord.key:
  for f: SignedRecord
  List<&2, U32>

# the record whose key is k, if k is the key of a record
law SignedRecord.from_key:
  for k: List<&2, U32>
  Maybe<&2, SignedRecord>

# the signature of the record f checks
law SignedRecord.signature_checks:
  for f: SignedRecord
  Bool

# the measure of the entry of the key k in a record set
law SignedRecordSet.entry_hash:
  for k: List<&2, U32>
  for u: Unit
  Shared.FixedLengthList(U32, 8n)

# the summaries x and y of two halves of a record set, combined
law SignedRecordSet.combine_hashes:
  for x: Shared.FixedLengthList(U32, 8n)
  for y: Shared.FixedLengthList(U32, 8n)
  Shared.FixedLengthList(U32, 8n)

# placeholders: SignedRecordSet names these in a def; their implementations
# replace these bodies
def SignedRecordSet.entry_hash(k, u):
  ?TODO

def SignedRecordSet.combine_hashes(x, y):
  ?TODO

# a set of records: a patricia_map from the key of each record to nothing,
# whose entries are measured by SignedRecordSet.entry_hash and whose summaries
# are combined by SignedRecordSet.combine_hashes
def SignedRecordSet() -> Data:
  PatriciaMap.PatriciaMap(
    ~Unit,
    ~(Shared.FixedLengthList(U32, 8n)),
    ~SignedRecordSet.entry_hash,
    ~SignedRecordSet.combine_hashes
  )

# Means: the key of a record reads back as that record, and a key that reads back
# as a record is that record's key.
# For free: two records with one key are the same record, and one record has one key,
# so a record set holds each record once and two nodes that hold the same records
# hold the same set; a key is all that a node needs to send a record, and all
# that the other node needs to read it.
# For the goal: Sync sends keys, and a node turns each key it receives into the
# record or into nothing, never into another record.
# Example: a vote of node a for slot 5 has one key; that key reads back as that
# vote, and words that are no key read as no record.
law SignedRecord.key_reads_back:
  for f: SignedRecord
  for k: List<&2, U32>
  {
    SignedRecord.from_key(SignedRecord.key(f)) == Some{f}: Maybe<&2, SignedRecord>
  }
    & (
      {
        SignedRecord.from_key(k) == Some{f}: Maybe<&2, SignedRecord>
      } -> {k == SignedRecord.key(f): List<&2, U32>}
    )

# Means: a record checks exactly when its signature checks for its words with
# its author's public key.
# For free: a record that nobody but its author could make checks only if its
# author made it (the signature assumption); a record checks on every node alike.
# For the goal: a node keeps a record only when it checks, so nothing that a
# stranger sends is kept unless its author signed it (Trust 3).
# Example: a vote whose signature is of other words does not check.
law SignedRecord.signature_checks_is_the_signature_check:
  for a: Shared.FixedLengthList(U32, 8n)
  for b: List<&2, U32>
  for s: List<&2, U32>
  {
    SignedRecord.signature_checks(
      SignedRecord{a, b, s}
    )
      == Signatures.Signature.checks(a, b, s): Bool
  }

# Means: the measure of an entry of a record set is the SHA-256 of its key, and
# two summaries combine as the SHA-256 of their words, one after the other.
# For free: with the summary law of patricia_map, the summary of each part of
# a record set is a Merkle hash of its records; two parts with different records
# have different summaries unless SHA-256 has a collision.
# For the goal: two nodes find the parts where their records differ by comparing
# summaries, and trust nothing but SHA-256 to do it (Trust 1); a Sync costs
# what differs, not what the nodes hold.
# Example: two nodes with the same records in a part have equal summaries of that
# part, so neither sends that part.
law SignedRecordSet.summaries_are_merkle_hashes:
  for k: List<&2, U32>
  for u: Unit
  for x: Shared.FixedLengthList(U32, 8n)
  for y: Shared.FixedLengthList(U32, 8n)
  {
    SignedRecordSet.entry_hash(k, u) == Sha256.Sha256.of_words(k): Shared.FixedLengthList(U32, 8n)
  }
    & {
      SignedRecordSet.combine_hashes(
        x,
        y
      )
        == Sha256.Sha256.of_words(
          List.append(
            &2,
            U32,
            Shared.FixedLengthList.to_list(U32, 8n, x),
            Shared.FixedLengthList.to_list(U32, 8n, y)
          )
        ): Shared.FixedLengthList(U32, 8n)
    }

# Reading record sets
# -------------------

# the record set s holds the key k
def Has(s: SignedRecordSet(), k: List<&2, U32>) -> Type:
  {
    Maybe.is_some(
      &2,
      Unit,
      PatriciaMap.PatriciaMap.get(
        ~Unit,
        ~(Shared.FixedLengthList(U32, 8n)),
        ~SignedRecordSet.entry_hash,
        ~SignedRecordSet.combine_hashes,
        s,
        k
      )
    )
      == True{}: Bool
  }

# k is the key of a record whose signature checks
def KeyOfChecked(k: List<&2, U32>) -> Type:
  Exists(
    SignedRecord,
    f => {
      SignedRecord.from_key(k) == Some{f}: Maybe<&2, SignedRecord>
    }
      & {SignedRecord.signature_checks(f) == True{}: Bool}
  )

# every key of s is the key of a record whose signature checks
def OnlyChecked(s: SignedRecordSet()) -> Type:
  @k: List<&2, U32> -> Has(s, k) -> KeyOfChecked(k)
