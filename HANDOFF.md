# Handoff

## The task

Implement and prove `src/vend_node/spec.bend`.

The spec is the whole contract of a Vend Node: what it needs and what it guarantees. It states
opaque types and operations, and laws about them. `src/vend_node/impl.bend` must fill every opaque
name and prove every law. When `bend src/vend_node/impl.bend --check-only` prints ALL PROOFS CHECK,
a Vend Node does what README.md promises.

## Priority

- The laws of `spec.bend` are by far the most important thing. If they hold, the work is done.
  Focus on them.
- Every other law in the repo is a means, not a goal. It states how the current code works.
- An agent may replace or delete any other law, if the laws of `spec.bend` still hold. List each one
  that you deleted, and why, for the human to accept.

## Rules

- Do not change any statement in `spec.bend`: no law, type, operation or comment. The human owns it.
- If a law looks false, unprovable or vague, stop and report it. Do not weaken it, and do not work
  around it.
- Every law must hold in its spirit, not vacuously. A proof that holds only because a type is empty,
  because a node never answers, never writes or never decides, or because an observer means nothing,
  is a failed proof.
- Proof quality does not matter. Any proof that the checker accepts, and that meets the spirit of
  the law, is good.
- Everything outside `spec.bend` is free. Rewrite, replace or delete any existing code. The current
  code is a resource, not a constraint.
- README.md is the canon. AGENTS.md applies.

## The spirit

- A decentralized version control system: every node is equal, syncs with any other node, and checks
  everything it receives.
- As fast as possible, and scalable to huge stores and resources.
- It works over deltas and shares every unchanged part, so it never keeps data it does not need.
- Correct by construction wherever a type can make a wrong value impossible.
- Optimal data structures from day one.
- Laziness and parallelism together, wherever they apply.
- Use every speed-up heuristic that keeps the laws true.

## How to work

- Use many agents in parallel.
- Every agent uses bend-synth as the first step of every proof: `bun run synth prove <file.bend>
  <def>`.
- Run the agents and bend-synth elsewhere, not on the human's machine.

## Trusted, and outside the spec

- Bend: its checker, compiler and runtime.
- Effects: the operating system, files and the network.
- SHA-256 and the signatures built on it: nobody can find two inputs with the same hash, or seal
  without the secret seed.
