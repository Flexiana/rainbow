# Maturity levels

Rainbow labels every result with a maturity level. The scale exists to stop
overclaiming: a level means what this file says and nothing else, and the level
of a chain is set by its WEAKEST link.

This repository -- the open core -- holds Levels 1-3: the kernel and the
mathematics. Levels 4-6 connect proved mathematics to code that runs; that
machinery (the verified code generator, the Clojure-subset semantics and its
compiler-correctness proofs, runtime certification) is Rainbow Pro, which uses
this repository as a library.

## The scale

**L1 -- research record.** Work exists and is written down. No claim that anyone
else can run it.

**L2 -- reproducible artifact.** A third party can re-run it from the repository
and get the same result. Content-addressed reports and replayable checkpoints
sit here: `lein verify` replays a checkpoint, and the kernel re-checks every
declaration in it on load.

**L3 -- proved theorem about a MODEL.** A kernel-checked, axiom-free theorem
about a mathematical model -- natural numbers, rationals, finite sums, an
algorithm's specification. NO claim about any executable. Most of this
repository is L3, and that is where the mathematics is. What L3 does not give
you is any link to code that runs.

**L4 -- output verification.** A real artifact produces an output, and the
kernel checks that particular output against a proved statement. A bug in the
artifact yields a REFUSED result, never a wrong one. It says nothing about
outputs the artifact was not run on, and it is not implementation correctness.

**L5 -- specification-to-program refinement.** A program exists as data, a
kernel-checked theorem says it denotes the specification, and a printer turns it
into code that runs. Every universally quantified theorem about the
specification transfers to the program. Some link in the chain to the executing
artifact is audited rather than proved.

**L6 -- machine-checked up to a stated trusted base.** Every link from the
proved specification to the artifact that executes is machine-checked, EXCEPT
the items on an explicitly published trusted-base list, each small enough to
audit by reading. For a program with side effects -- data arriving from sensors,
messages, clocks -- the claim additionally carries an ENVIRONMENT CONTRACT: the
assumptions about the world (sensor fidelity, timing, delivery) under which the
theorems apply, stated as premises, never hidden. Concretely an L6 claim needs:

- theorems that are universal over the input stream, not about chosen inputs;
- a trusted-base list (see `doc/trusted-base.md` for the part every claim shares);
- an environment contract, for anything that interacts with the world;
- runtime certification of every step, with a safe fallback when a step's
  certificate does not check -- so a violated assumption degrades to a refusal,
  not to a wrong action.

"Machine-checked" is not "trust-free". An L6 claim that does not name its
trusted base and its environment contract is not an L6 claim.

## Two rules that decide most arguments

**Tests never constitute a link, at any coverage.** A test compares an output to
an expected value chosen by a person. A change that breaks both the same way
passes. That is a different kind of evidence from a proof, not a weaker amount
of the same kind.

**The number means the WEAKEST link, not the strongest.** A chain with a
beautiful refinement proof and one unproved, unlisted step is set by that step.
There is no "L5.5" and no "L6 with a caveat": either the caveat is on the
trusted-base list, or the level is lower.
