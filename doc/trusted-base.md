# What you have to trust

A proof checked by Rainbow is exactly as trustworthy as the code that checked it.
This file lists that code. Everything not on this list is checked BY it: the
mathematics, the tactics that build proofs, the proof search -- a bug anywhere
else produces a rejected proof, never an accepted false one.

## The kernel: 1,661 lines

| file | lines | role |
|---|---|---|
| `src/rainbow/kernel.clj` | 1248 | type checking, definitional equality, reduction, natural-number literals and the six native nat operations, inductive types and recursors, universe levels |
| `src/rainbow/term.clj` | 320 | the term language: binders, substitution (skipping subterms with nothing to change), de Bruijn indices, universe-level equivalence |
| `src/rainbow/environment.clj` | 48 | declarations stored by content id; name resolution |
| `src/rainbow/canonical.clj` | 45 | canonical encoding and the content hash that names every declaration |
| **total** | **1661** | |

The size is pinned: a release test (`v1_release_test`) fails if these four files
change length, so growth in the trusted base is always a visible, deliberate
decision. 1.1.0 grew it from 1,198 lines (1.0.1; the 1.0.0 tag had 1,200) to make checking 24-123x faster: native
natural-number arithmetic pinned to six definitions by content id (each tested against
the definition's own unary reduction), and substitution that skips unchanged subterms.
1.4.2 grew it to 1,471 lines with two soundness fixes for inductive types (see the CHANGELOG):
constructor fields are checked against the inductive type's universe, and a proposition with
two or more constructors can no longer be eliminated into a larger universe.
1.4.4 grew it to 1,548 lines: universe levels are compared by value (`term/level-equivalent?`,
so correct proofs are no longer refused over an incomplete level normal form), and constructors
and recursors carry the axioms their types mention.
1.5.0 grew it to 1,661 lines with lazy conversion in type checking: `check*` first compares types
by head reduction, congruence on equal heads and one-at-a-time unfolding, and falls back to the
unchanged full-normalisation comparison when that fails.

The nested inductive-binder identity repair changes content IDs for affected
blocks. Earlier kernels could conflate distinct field types and accept an
axiom-free proof of False. Rebuild affected blocks and their dependents, and
replay proof artifacts with the repaired kernel; a pre-repair pass is not a
soundness clearance. Unaffected IDs retain their encoding. Regression tests
exercise the original false-proof construction and require its rejection.

## Below the kernel

The kernel itself runs on, and so trusts:

- the Clojure reader and compiler, and the JVM;
- SHA-256 as implemented by the JDK (content ids; a collision would let two
  declarations share a name).

## What is NOT trusted

- **Tactics** (the ring normalisers for naturals and rationals, the `Bool.rec`
  case-split helpers): they build proof terms, which the kernel then checks. A
  wrong tactic yields a rejected term.
- **Elaboration** (`rainbow.elaborate`): it turns surface syntax into terms; the
  kernel checks the result.
- **Checkpoints**: a checkpoint is a list of declarations, and loading one
  re-checks every declaration. A tampered checkpoint does not replay.
- **Axioms** are not hidden. A logical principle (for example a classical one)
  enters only as an explicit axiom declaration (`rainbow.math.profile`), and
  every theorem's axiom profile -- the axioms it transitively depends on -- is
  computed by the kernel (`kernel/axioms`). `lein verify` prints it per theorem,
  and the tests assert each covered theorem's profile: empty, except eight named
  classical theorems in `set_boundary.clj` and `set_union.clj`.

## Beyond Level 3

A claim that a running program is correct (Levels 4-6, see
`doc/maturity-levels.md`) trusts more than the kernel: the meaning of the source
and target languages, the printer between proved terms and executable text, the
runtime's arithmetic, and -- for programs that touch the world -- an environment
contract. Each such claim must publish its own list, extending this one.
