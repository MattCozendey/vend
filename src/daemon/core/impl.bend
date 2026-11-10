# bend-lint: expect-file bend-lint-rules/no_unused/imports@warning -- this file gathers the proofs of the core: a check of it checks each of them
import Base
import ./proofs/agreement.bend as ProofAgreement
import ./proofs/finality.bend as ProofFinality
import ./proofs/histories.bend as ProofHistories
import ./proofs/lines.bend as ProofLines
import ./proofs/logs.bend as ProofLogs
import ./proofs/merges.bend as ProofMerges
import ./proofs/paths.bend as ProofPaths
import ./proofs/rounds.bend as ProofRounds
import ./proofs/trees.bend as ProofTrees
import ./proofs/waits.bend as ProofWaits
import ./spec.bend as Spec

# The proofs of the core's laws.
