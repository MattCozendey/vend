import Base
import ../shared/shared.bend as Shared

# A signer makes signatures of words with a secret, and a public key checks
# them. A signer is a Type, not Data, so a program can never copy it and sign
# twice from one state. Nobody without the secret can make a signature that
# checks: that is assumed (it rests on SHA-256), not proven (Trust 1).

# a signer: a secret, and what it has signed
law Signer:
  Type

# the signer of the secret seed, before it signs anything
law Signer.of_seed:
  for seed: Shared.Row(U32, 8n)
  Signer

# the public key of the signer s, and s
law Signer.public_key:
  for s: Signer
  Shared.Row(U32, 8n) & Signer

# how many more signatures the signer s can make, and s
law Signer.remaining:
  for s: Signer
  Nat & Signer

# a signature of the words m, if s can still make one, and the signer after it
law Signer.sign:
  for s: Signer
  for m: List<&2, U32>
  Maybe<&2, List<&2, U32>> & Signer

# the signature sig of the words m checks with the public key k
law Signature.checks:
  for k: Shared.Row(U32, 8n)
  for m: List<&2, U32>
  for sig: List<&2, U32>
  Bool

# Means: a signature that a signer makes for some words checks with its public
# key for those words; signing keeps the public key; and a signer that can make
# one more signature makes it, and can then make one less.
# For free: every signature that a signer ever makes, at any point of its life,
# checks with the key it had at the start; a node's name, which carries its
# key, stays right for good.
# For the goal: a vote that a node signs is kept by every node that checks it
# (Trust 3), and a node signs until it has used up what its signer can make.
# Example: a signer with 5 signatures left signs a vote; the signature checks
# with its key, and 4 are left.
law Signer.signing_checks_keeps_key_and_uses_one:
  for s: Signer
  for m: List<&2, U32>
  (
    @sig: List<
      &2,
      U32> -> {
      Pair.fst(
        Maybe<&2, List<&2, U32>>,
        Signer,
        Signer.sign(s, m)
      )
        == Some{sig}: Maybe<&2, List<&2, U32>>
    } -> {
      Signature.checks(
        Pair.fst(Shared.Row(U32, 8n), Signer, Signer.public_key(s)),
        m,
        sig
      )
        == True{}: Bool
    }
  )
    & {
      Pair.fst(
        Shared.Row(U32, 8n),
        Signer,
        Signer.public_key(Pair.snd(Maybe<&2, List<&2, U32>>, Signer, Signer.sign(s, m)))
      )
        == Pair.fst(Shared.Row(U32, 8n), Signer, Signer.public_key(s)): Shared.Row(U32, 8n)
    }
    & (
      @n: Nat -> {
        Pair.fst(Nat, Signer, Signer.remaining(s)) == 1n+n: Nat
      } -> {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Pair.fst(Maybe<&2, List<&2, U32>>, Signer, Signer.sign(s, m))
        )
          == True{}: Bool
      }
        & {
          Pair.fst(
            Nat,
            Signer,
            Signer.remaining(Pair.snd(Maybe<&2, List<&2, U32>>, Signer, Signer.sign(s, m)))
          )
            == n: Nat
        }
    )

# Means: a new signer can make at least 2^20 signatures.
# For free: with the law above, the first 2^20 signatures of a signer are all
# made, and all check.
# For the goal: a node casts its votes for a long life before it needs a new
# key; a signer that never signs cannot pass this law.
# Example: a signer made from any seed signs its 1000th vote.
law Signer.of_seed_signs_at_least_2_to_the_20:
  for seed: Shared.Row(U32, 8n)
  {
    Nat.is_le(
      U32.to_nat(1048576),
      Pair.fst(Nat, Signer, Signer.remaining(Signer.of_seed(seed)))
    )
      == True{}: Bool
  }
