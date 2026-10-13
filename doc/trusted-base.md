# What you have to trust

A proof checked by Rainbow is exactly as trustworthy as the code that checked it.
This file lists that code. Everything not on this list is checked BY it: the
mathematics, the tactics that build proofs, the proof search -- a bug anywhere
else produces a rejected proof, never an accepted false one.

## The kernel: 1,200 lines

| file | lines | role |
|---|---|---|
| `src/rainbow/kernel.clj` | 915 | type checking, definitional equality, reduction, inductive types and recursors, universe levels |
| `src/rainbow/term.clj` | 196 | the term language: binders, substitution, de Bruijn indices |
| `src/rainbow/environment.clj` | 48 | declarations stored by content id; name resolution |
| `src/rainbow/canonical.clj` | 41 | canonical encoding and the content hash that names every declaration |
| **total** | **1200** | |

The size is pinned: a release test (`v1_release_test`) fails if these four files
change length, so growth in the trusted base is always a visible, deliberate
decision.

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
  and the tests assert an empty profile for the theorems they cover.

## Beyond Level 3

A claim that a running program is correct (Levels 4-6, see
`doc/maturity-levels.md`) trusts more than the kernel: the meaning of the source
and target languages, the printer between proved terms and executable text, the
runtime's arithmetic, and -- for programs that touch the world -- an environment
contract. Each such claim must publish its own list, extending this one.
