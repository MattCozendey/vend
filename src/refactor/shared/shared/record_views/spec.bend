import Base
import ../shared/shared/shared/part_store/spec.bend as PartStore
import ../shared/shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/word_list_sets/spec.bend as WordListSets
import ../shared/shared/signed_records/spec.bend as SignedRecords
import ../shared/slot_consensus/spec.bend as SlotConsensus

# Record views read what the records of a record set are, through hooks that
# read the words of a record: the ballots among them and the keep claims among
# them. A ballot or a claim counts only as its record's author's: its voter or
# keeper is the author, and a ballot's key is its record's key.

# the words of a ballot, as its record holds them: its step, its index, its
# round, and its action
type BallotBody is Data:
  BallotBody{step: SlotConsensus.Step, index: Nat, round: Nat, action: SlotConsensus.BallotAction}

# the ballots among the records of rs, as ballot_of reads their words
law RecordViews.ballots:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, BallotBody>
  for rs: SignedRecords.SignedRecordSet()
  List<&2, SlotConsensus.Ballot>

# the keep claims among the records of rs, as claim_of reads their words
law RecordViews.claims:
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for rs: SignedRecords.SignedRecordSet()
  List<&2, PartStore.KeepClaim>

# the record set rs holds the key k of a record whose author is v and whose
# words ballot_of reads as the ballot of the step s, index i, round r and
# action a
def IsBallot(
  ~ballot_of: List<&2, U32> -> Maybe<&2, BallotBody>,
  rs: SignedRecords.SignedRecordSet(),
  k: List<&2, U32>,
  v: List<&2, U32>,
  s: SlotConsensus.Step,
  i: Nat,
  r: Nat,
  a: SlotConsensus.BallotAction
) -> Type:
  SignedRecords.Has(
    rs,
    k
  )
    & Exists(
      Shared.FixedLengthList(U32, 8n),
      au => Exists(
        List<&2, U32>,
        bo => Exists(
          List<&2, U32>,
          sg => {
            SignedRecords.SignedRecord.from_key(
              k
            )
              == Some{SignedRecords.SignedRecord{au, bo, sg}}: Maybe<&2, SignedRecords.SignedRecord>
          }
            & (
              {
                ballot_of(bo) == Some{BallotBody{s, i, r, a}}: Maybe<&2, BallotBody>
              }
                & {Shared.FixedLengthList.to_list(U32, 8n, au) == v: List<&2, U32>}
            )
        )
      )
    )

# the record set rs holds the key of a record whose author is v and whose words
# claim_of reads as a claim to keep the part of the hash h
def IsClaim(
  ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>,
  rs: SignedRecords.SignedRecordSet(),
  v: List<&2, U32>,
  h: Shared.FixedLengthList(U32, 8n)
) -> Type:
  Exists(
    List<&2, U32>,
    k => SignedRecords.Has(
      rs,
      k
    )
      & Exists(
        Shared.FixedLengthList(U32, 8n),
        au => Exists(
          List<&2, U32>,
          bo => Exists(
            List<&2, U32>,
            sg => {
              SignedRecords.SignedRecord.from_key(
                k
              )
                == Some{
                  SignedRecords.SignedRecord{au, bo, sg}
                }: Maybe<&2, SignedRecords.SignedRecord>
            }
              & (
                {
                  claim_of(bo) == Some{h}: Maybe<&2, Shared.FixedLengthList(U32, 8n)>
                }
                  & {Shared.FixedLengthList.to_list(U32, 8n, au) == v: List<&2, U32>}
              )
          )
        )
      )
  )

# the parts pa and pb are the same, when their keepers are (same_keepers)
def same_claim.parts(
  same_keepers: Bool,
  pa: Shared.FixedLengthList(U32, 8n),
  pb: Shared.FixedLengthList(U32, 8n)
) -> Bool:
  match same_keepers:
    case False{}:
      False{}
    case True{}:
      PartStore.same_hash(pa, pb)

# a and b are the same claim
def same_claim(a: PartStore.KeepClaim, b: PartStore.KeepClaim) -> Bool:
  match a b:
    case PartStore.KeepClaim{ka, pa} PartStore.KeepClaim{kb, pb}:
      same_claim.parts(WordListSets.same(ka, kb), pa, pb)

# Laws
# ----

# Means: the ballots of a record set are exactly the ballots that its records'
# words are, each with its record's author as voter and its record's key as key.
# For free: a record whose author is not the voter that its words name is no
# ballot, so nobody votes in another's name; more records give more ballots.
# For the goal: slot consensus reads ballots, owner groups read decisions, and
# both rest on records whose signatures check (Trust 3).
# Example: a record by node a whose words read as a vote of slot 5 is a ballot
# of a for slot 5, under that record's key.
law RecordViews.ballots_are_records:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, BallotBody>
  for rs: SignedRecords.SignedRecordSet()
  for k: List<&2, U32>
  for v: List<&2, U32>
  for s: SlotConsensus.Step
  for i: Nat
  for r: Nat
  for a: SlotConsensus.BallotAction
  (
    {
      List.contains(
        ~SlotConsensus.Ballot,
        ~SlotConsensus.Ballot.same,
        RecordViews.ballots(~ballot_of, rs),
        SlotConsensus.Ballot{k, v, s, i, r, a}
      )
        == True{}: Bool
    } -> IsBallot(~ballot_of, rs, k, v, s, i, r, a)
  )
    & (
      IsBallot(
        ~ballot_of,
        rs,
        k,
        v,
        s,
        i,
        r,
        a
      ) -> {
        List.contains(
          ~SlotConsensus.Ballot,
          ~SlotConsensus.Ballot.same,
          RecordViews.ballots(~ballot_of, rs),
          SlotConsensus.Ballot{k, v, s, i, r, a}
        )
          == True{}: Bool
      }
    )

# Means: the keep claims of a record set are exactly the claims that its
# records' words are, each with its record's author as keeper.
# For free: nobody claims to keep a part in another's name; more records give
# more claims.
# For the goal: a node drops a part only on claims that their keepers signed
# (Behavior 3).
# Example: a record by node b whose words read as a claim on the hash H is a
# claim of b on H.
law RecordViews.claims_are_records:
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for rs: SignedRecords.SignedRecordSet()
  for v: List<&2, U32>
  for h: Shared.FixedLengthList(U32, 8n)
  (
    {
      List.contains(
        ~PartStore.KeepClaim,
        ~same_claim,
        RecordViews.claims(~claim_of, rs),
        PartStore.KeepClaim{v, h}
      )
        == True{}: Bool
    } -> IsClaim(~claim_of, rs, v, h)
  )
    & (
      IsClaim(
        ~claim_of,
        rs,
        v,
        h
      ) -> {
        List.contains(
          ~PartStore.KeepClaim,
          ~same_claim,
          RecordViews.claims(~claim_of, rs),
          PartStore.KeepClaim{v, h}
        )
          == True{}: Bool
      }
    )
