import Base
import ../shared/shared/patricia_map/spec.bend as PatriciaMap
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/signed_records/spec.bend as SignedRecords

# Record sync: two nodes exchange messages (words) until one of them has
# nothing more to say, and then each holds the records of both. A node opens
# with a message; each side takes in each message it gets, keeping only
# records whose signatures check, and replies; an empty reply ends the sync.
# What the messages say (summaries of parts of the record set, then the
# records of the parts that differ) is the implementation's choice: the laws
# below say what every choice must do. A peer that does not follow the
# protocol can make a sync incomplete, but it can never make a node keep a
# record that does not check, nor lose one.

# the first message that a node with the record set s sends
law RecordSync.opening:
  for s: SignedRecords.SignedRecordSet()
  List<&2, U32>

# the record set s after the node takes in the message m
law RecordSync.take:
  for s: SignedRecords.SignedRecordSet()
  for m: List<&2, U32>
  SignedRecords.SignedRecordSet()

# the reply of a node with the record set s to the message m: empty when it has
# nothing more to say
law RecordSync.reply:
  for s: SignedRecords.SignedRecordSet()
  for m: List<&2, U32>
  List<&2, U32>

# Reading record sets
# -------------------

# the record set s holds the key k
def Has(s: SignedRecords.SignedRecordSet(), k: List<&2, U32>) -> Type:
  {
    Maybe.is_some(
      &2,
      Unit,
      PatriciaMap.PatriciaMap.get(
        ~Unit,
        ~(Shared.FixedLengthList(U32, 8n)),
        ~SignedRecords.SignedRecordSet.entry_hash,
        ~SignedRecords.SignedRecordSet.combine_hashes,
        s,
        k
      )
    )
      == True{}: Bool
  }

# k is the key of a record whose signature checks
def KeyOfChecked(k: List<&2, U32>) -> Type:
  Exists(
    SignedRecords.SignedRecord,
    f => {
      SignedRecords.SignedRecord.from_key(k) == Some{f}: Maybe<&2, SignedRecords.SignedRecord>
    }
      & {SignedRecords.SignedRecord.signature_checks(f) == True{}: Bool}
  )

# every key of s is the key of a record whose signature checks
def OnlyChecked(s: SignedRecords.SignedRecordSet()) -> Type:
  @k: List<&2, U32> -> Has(s, k) -> KeyOfChecked(k)

# SHA-256 has no collision on the parts of a and b with the keys from lo on,
# below hi when hi is there: two such parts with equal summaries are the same
def CollisionFreeOn(
  a: SignedRecords.SignedRecordSet(),
  b: SignedRecords.SignedRecordSet(),
  lo: List<&2, U32>,
  hi: Maybe<&2, List<&2, U32>>
) -> Type:
  match hi:
    case None{}:
      {
        PatriciaMap.PatriciaMap.summary(
          ~Unit,
          ~(Shared.FixedLengthList(U32, 8n)),
          ~SignedRecords.SignedRecordSet.entry_hash,
          ~SignedRecords.SignedRecordSet.combine_hashes,
          Pair.snd(
            SignedRecords.SignedRecordSet(),
            SignedRecords.SignedRecordSet(),
            PatriciaMap.PatriciaMap.split(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              a,
              lo
            )
          )
        )
          == PatriciaMap.PatriciaMap.summary(
            ~Unit,
            ~(Shared.FixedLengthList(U32, 8n)),
            ~SignedRecords.SignedRecordSet.entry_hash,
            ~SignedRecords.SignedRecordSet.combine_hashes,
            Pair.snd(
              SignedRecords.SignedRecordSet(),
              SignedRecords.SignedRecordSet(),
              PatriciaMap.PatriciaMap.split(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                b,
                lo
              )
            )
          ): Maybe<&2, Shared.FixedLengthList(U32, 8n)>
      }
        -> {
          Pair.snd(
            SignedRecords.SignedRecordSet(),
            SignedRecords.SignedRecordSet(),
            PatriciaMap.PatriciaMap.split(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              a,
              lo
            )
          )
            == Pair.snd(
              SignedRecords.SignedRecordSet(),
              SignedRecords.SignedRecordSet(),
              PatriciaMap.PatriciaMap.split(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                b,
                lo
              )
            ): SignedRecords.SignedRecordSet()
        }
    case Some{h}:
      {
        PatriciaMap.PatriciaMap.summary(
          ~Unit,
          ~(Shared.FixedLengthList(U32, 8n)),
          ~SignedRecords.SignedRecordSet.entry_hash,
          ~SignedRecords.SignedRecordSet.combine_hashes,
          Pair.fst(
            SignedRecords.SignedRecordSet(),
            SignedRecords.SignedRecordSet(),
            PatriciaMap.PatriciaMap.split(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              Pair.snd(
                SignedRecords.SignedRecordSet(),
                SignedRecords.SignedRecordSet(),
                PatriciaMap.PatriciaMap.split(
                  ~Unit,
                  ~(Shared.FixedLengthList(U32, 8n)),
                  ~SignedRecords.SignedRecordSet.entry_hash,
                  ~SignedRecords.SignedRecordSet.combine_hashes,
                  a,
                  lo
                )
              ),
              h
            )
          )
        )
          == PatriciaMap.PatriciaMap.summary(
            ~Unit,
            ~(Shared.FixedLengthList(U32, 8n)),
            ~SignedRecords.SignedRecordSet.entry_hash,
            ~SignedRecords.SignedRecordSet.combine_hashes,
            Pair.fst(
              SignedRecords.SignedRecordSet(),
              SignedRecords.SignedRecordSet(),
              PatriciaMap.PatriciaMap.split(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                Pair.snd(
                  SignedRecords.SignedRecordSet(),
                  SignedRecords.SignedRecordSet(),
                  PatriciaMap.PatriciaMap.split(
                    ~Unit,
                    ~(Shared.FixedLengthList(U32, 8n)),
                    ~SignedRecords.SignedRecordSet.entry_hash,
                    ~SignedRecords.SignedRecordSet.combine_hashes,
                    b,
                    lo
                  )
                ),
                h
              )
            )
          ): Maybe<&2, Shared.FixedLengthList(U32, 8n)>
      }
        -> {
          Pair.fst(
            SignedRecords.SignedRecordSet(),
            SignedRecords.SignedRecordSet(),
            PatriciaMap.PatriciaMap.split(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              Pair.snd(
                SignedRecords.SignedRecordSet(),
                SignedRecords.SignedRecordSet(),
                PatriciaMap.PatriciaMap.split(
                  ~Unit,
                  ~(Shared.FixedLengthList(U32, 8n)),
                  ~SignedRecords.SignedRecordSet.entry_hash,
                  ~SignedRecords.SignedRecordSet.combine_hashes,
                  a,
                  lo
                )
              ),
              h
            )
          )
            == Pair.fst(
              SignedRecords.SignedRecordSet(),
              SignedRecords.SignedRecordSet(),
              PatriciaMap.PatriciaMap.split(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                Pair.snd(
                  SignedRecords.SignedRecordSet(),
                  SignedRecords.SignedRecordSet(),
                  PatriciaMap.PatriciaMap.split(
                    ~Unit,
                    ~(Shared.FixedLengthList(U32, 8n)),
                    ~SignedRecords.SignedRecordSet.entry_hash,
                    ~SignedRecords.SignedRecordSet.combine_hashes,
                    b,
                    lo
                  )
                ),
                h
              )
            ): SignedRecords.SignedRecordSet()
        }

# SHA-256 has no collision on any part of a and b
def CollisionFree(a: SignedRecords.SignedRecordSet(), b: SignedRecords.SignedRecordSet()) -> Type:
  @lo: List<&2, U32> -> @hi: Maybe<&2, List<&2, U32>> -> CollisionFreeOn(a, b, lo, hi)

# Sessions
# --------

# a sync in which the node with the record set x sends the message m to the
# node with the record set y ends within n messages, with x2 and y2 as their
# record sets: when y's reply is empty, y takes in m and x stays; otherwise y
# takes in m and the sync goes on with y sending its reply to x
def Ends(
  n: Nat,
  x: SignedRecords.SignedRecordSet(),
  y: SignedRecords.SignedRecordSet(),
  m: List<&2, U32>,
  x2: SignedRecords.SignedRecordSet(),
  y2: SignedRecords.SignedRecordSet()
) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+k:
      (
        {
          RecordSync.reply(y, m) == []: List<&2, U32>
        }
          & (
            {
              x2 == x: SignedRecords.SignedRecordSet()
            }
              & {y2 == RecordSync.take(y, m): SignedRecords.SignedRecordSet()}
          )
      )
        | (
          (
            {RecordSync.reply(y, m) == []: List<&2, U32>} -> Empty
          )
            & Ends(k, RecordSync.take(y, m), x, RecordSync.reply(y, m), y2, x2)
        )

# Laws
# ----

# Means: taking in a message never loses a record that the node holds.
# For free: a sync with a faulty peer, or one cut off halfway, leaves a node
# with at least what it had; records only accumulate.
# For the goal: nothing that a peer sends can make a node forget a record
# (Behavior 1, Trust 3), and partial syncs are safe to stop at any point.
# Example: a node that holds a vote still holds it after a message from a peer
# that holds nothing.
law RecordSync.take_keeps:
  for s: SignedRecords.SignedRecordSet()
  for m: List<&2, U32>
  for k: List<&2, U32>
  Has(s, k) -> Has(RecordSync.take(s, m), k)

# Means: a record that a node holds after taking in a message was already
# there, or its signature checks.
# For free: a record set that holds only records that check keeps holding only
# such records, whatever any peer sends.
# For the goal: nothing that a stranger sends is kept unless its author signed
# it (Trust 3).
# Example: a message carrying a vote with a forged signature adds nothing.
law RecordSync.take_adds_only_checked:
  for s: SignedRecords.SignedRecordSet()
  for m: List<&2, U32>
  for k: List<&2, U32>
  Has(RecordSync.take(s, m), k) -> (Has(s, k) | KeyOfChecked(k))

# Means: every sync between two nodes that follow the protocol ends.
# For free: a sync needs no timer to finish; a node can serve one sync after
# another.
# For the goal: two nodes catch up with each other by themselves (Behavior 1).
# Example: two nodes with the same records end after the opening and an empty
# reply.
law RecordSync.ends:
  for a: SignedRecords.SignedRecordSet()
  for b: SignedRecords.SignedRecordSet()
  Exists(
    Nat,
    n => Exists(
      SignedRecords.SignedRecordSet(),
      a2 => Exists(
        SignedRecords.SignedRecordSet(),
        b2 => Ends(n, a, b, RecordSync.opening(a), a2, b2)
      )
    )
  )

# Means: when a sync between two nodes that hold only records that check ends,
# and SHA-256 has no collision on their parts, each node holds exactly the
# records of both.
# For free: after a sync both nodes are in the same state (the map law: same
# entries, same map), so they give the same answers; a sync sends only what
# differs, as the summaries of equal parts are equal.
# For the goal: two nodes that sync hold the same records, whatever each held
# before and in whatever order (Behavior 1), and the only trust a sync needs is
# SHA-256 (Trust 1).
# Example: node a holds votes 1 and 2, node b holds votes 2 and 3; after a sync
# both hold votes 1, 2 and 3.
law RecordSync.ends_with_both:
  for n: Nat
  for a: SignedRecords.SignedRecordSet()
  for b: SignedRecords.SignedRecordSet()
  for a2: SignedRecords.SignedRecordSet()
  for b2: SignedRecords.SignedRecordSet()
  for k: List<&2, U32>
  Ends(n, a, b, RecordSync.opening(a), a2, b2)
    -> OnlyChecked(a)
    -> OnlyChecked(b)
    -> CollisionFree(a, b)
    -> {
      Maybe.is_some(
        &2,
        Unit,
        PatriciaMap.PatriciaMap.get(
          ~Unit,
          ~(Shared.FixedLengthList(U32, 8n)),
          ~SignedRecords.SignedRecordSet.entry_hash,
          ~SignedRecords.SignedRecordSet.combine_hashes,
          a2,
          k
        )
      )
        == Bool.or(
          Maybe.is_some(
            &2,
            Unit,
            PatriciaMap.PatriciaMap.get(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              a,
              k
            )
          ),
          Maybe.is_some(
            &2,
            Unit,
            PatriciaMap.PatriciaMap.get(
              ~Unit,
              ~(Shared.FixedLengthList(U32, 8n)),
              ~SignedRecords.SignedRecordSet.entry_hash,
              ~SignedRecords.SignedRecordSet.combine_hashes,
              b,
              k
            )
          )
        ): Bool
    }
      & {
        Maybe.is_some(
          &2,
          Unit,
          PatriciaMap.PatriciaMap.get(
            ~Unit,
            ~(Shared.FixedLengthList(U32, 8n)),
            ~SignedRecords.SignedRecordSet.entry_hash,
            ~SignedRecords.SignedRecordSet.combine_hashes,
            b2,
            k
          )
        )
          == Bool.or(
            Maybe.is_some(
              &2,
              Unit,
              PatriciaMap.PatriciaMap.get(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                a,
                k
              )
            ),
            Maybe.is_some(
              &2,
              Unit,
              PatriciaMap.PatriciaMap.get(
                ~Unit,
                ~(Shared.FixedLengthList(U32, 8n)),
                ~SignedRecords.SignedRecordSet.entry_hash,
                ~SignedRecords.SignedRecordSet.combine_hashes,
                b,
                k
              )
            )
          ): Bool
      }
