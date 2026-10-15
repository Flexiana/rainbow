# Rainbow

[![ci](https://github.com/flexiana/rainbow/actions/workflows/ci.yml/badge.svg)](https://github.com/flexiana/rainbow/actions/workflows/ci.yml)

**A theorem prover in Clojure that treats proofs as data.**

Rainbow checks mathematics with a small dependent-type kernel — 1,364 lines you
can read in an afternoon — and stores everything it checks as plain, immutable,
content-addressed EDN: terms, declarations, proofs, failures and their
provenance. A proof is a value. You can store it, diff it, hash it, ship it and
re-check it, and a verified result becomes a building block for the next one.

This repository is the open core: the kernel, the elaborator and tactics, a
baseline proof search, and a corpus of about 5,000 machine-checked
declarations — natural numbers, rationals and signed rationals, finite sums,
order, convexity and duality, finite matrices, Markov chains, and kernel-checked
theorems about the decision step of each of the 222 algorithms in the *Applied
Higher-Order Functions* operations-research catalogue.

```sh
git clone https://github.com/flexiana/rainbow && cd rainbow
lein verify rainbow.math.finite.rational-argmax
```

```
checkpoint artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz replayed
OK    rainbow.math.finite.rational-argmax (15 theorems: 13 for all inputs, 2 worked instances)
       checked   instance  bool/false-not-true  axiom-free
       checked   instance  bool/true-not-false  axiom-free
       checked   for-all   decision/finite-nnrat-argmax-dominates  axiom-free
       ...
```

That command replays a checkpoint (every declaration in it goes back through
the kernel), installs a module, re-checks each of its theorems, and prints for
each one whether it holds **for all inputs** or is a **worked instance** about
specific values, and which axioms it depends on. The exit code is non-zero if
anything fails, so it works as a CI gate.

## Why another prover

Most "verified" claims fail in the same place: a theorem about a model, a
program that allegedly implements the model, and nothing checking the link.
Rainbow was built to be exact about that gap rather than to hide it.

- **The trusted base is small and pinned.** Four files, 1,364 lines, and a
  release test fails if they change length. Search, tactics, elaboration and
  checkpoint loading are all untrusted: they propose terms, the kernel decides.
  See [`doc/trusted-base.md`](doc/trusted-base.md).
- **Every result carries a maturity level, set by its weakest link.** A
  theorem about a model (Level 3) is not a verified program (Level 6), and tests
  never count as a link at any coverage. See
  [`doc/maturity-levels.md`](doc/maturity-levels.md).
- **Proofs are data, so evidence is reproducible.** Checkpoints are
  content-addressed; `lein reproduce` rebuilds one from source and compares
  hashes. Nothing in a report is a remembered number.
- **No hidden axioms.** A logical principle enters only as an explicit axiom
  declaration, and the kernel computes each theorem's axiom profile. The
  corpus's tests assert an empty profile for the theorems they cover.
- **No inflated statements.** The kernel classifies every theorem as holding for
  all inputs or as a worked instance, and `lein verify` prints which. Of the
  415 algorithm proof modules, 48 prove something for all inputs;
  the rest check worked instances of the algorithm's decision step, and say so.
  Classical guarantees (optimality, convergence, approximation ratios) are claimed
  only where a theorem states them. See [`doc/claims.md`](doc/claims.md).

## Getting started

You need a JDK and [Leiningen](https://leiningen.org).

```sh
lein verify <namespace> ...          # re-check a module's theorems, print their axioms
lein reproduce <milestone> ...       # rebuild a checkpoint from source, compare its content id
lein verify --bundle [--reductions N] <file.edn> ...
                                     # re-check proofs made elsewhere (a proof bundle) with the kernel alone
lein reproduce --all                 # every reproducible milestone
lein test                            # the whole suite (long; see below)
scripts/run-suite-chunked.sh 40      # the suite in fresh-JVM chunks of 40 namespaces
```

The full suite is about 1,600 tests and 16,000 assertions and takes hours,
because many tests replay large checkpoints through the kernel. Run a single
namespace with `lein test rainbow.math.rational.nnrat.ring-test`.

**What a theorem claims:** [`doc/claims.md`](doc/claims.md).
**Look around:** [`doc/tour.md`](doc/tour.md) walks through the kernel, a
small theorem, a ring tactic, an algorithm proof and a milestone, in that
order. [`doc/corpus.md`](doc/corpus.md) indexes every proof module by topic.

## What a proof looks like

A theorem is a map. This one, from
[`math/rational/nnrat/identities.clj`](src/rainbow/math/rational/nnrat/identities.clj),
says that adding zero on the right leaves a non-negative rational unchanged up to
equivalence (rationals are pairs, so `x + 0` is equal to `x` only up to
cross-multiplication):

```clojure
(def add-zero-right-spec
  {:name 'nnrat/add-zero-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (add 'value nnrat-zero) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          ...                                   ; the proof term, built from smaller lemmas
```

The `:type` is the statement and the `:value` is the proof; both are ordinary
Clojure data. A module lists its specs in `theorem-specs`, declares the modules it
builds on in `deps`, and installs its specs through the kernel, which type-checks
each `:value` against its `:type`. The installed declaration is named by the hash
of its content. [`doc/tour.md`](doc/tour.md) reads a module end to end;
[`doc/modules.md`](doc/modules.md) explains the module format.

## What is in the box

| | |
|---|---|
| `src/rainbow/{kernel,term,environment,canonical}.clj` | the trusted kernel, 1,364 lines |
| `src/rainbow/math/` | foundations: nat, rationals, signed rationals, sums, finite types, sets, linear algebra, analysis |
| `src/rainbow/algorithms/` | algorithm guarantees (`proofs/`) and the reference implementations they are about |
| `src/rainbow/milestones/` | the drivers that built the corpus checkpoints, one per result |
| `src/rainbow/history/` | the bootstrap chronology: the first direct-term corpus, the first tactic, the Lean round trip, the Mathlib experiments |
| `src/rainbow/foreign/`, `foreign/lean/` | the Lean 4 bridge: export, import, a verified round trip |
| `artifacts/` | checkpoints and reports; declarations stored once in `artifacts/store/` |
| `doc/` | maturity levels, what a theorem claims, trusted base, module format, tour, corpus index |

## Rainbow Pro

Rainbow Pro is the commercial layer, built by Flexiana on top of this
repository and using it as a library. It turns proved specifications into
Clojure that runs: a Clojure-subset semantics with compiler-correctness proofs,
a code generator, 1,000 program families with certificate checkers, and the
proof automation. Everything Pro proves is checked by the kernel in this
repository. Pro's programs currently reach Level 5; Level 6, machine-checked up
to a stated trusted base, is the target. Ask us at
[flexiana.com](https://flexiana.com/contact).

## Status and honesty

Rainbow is past its v1.0 milestone. It is also young: the API will change, and the documentation is thinner than the
code. What it does *not* claim is listed in the documentation next to what it
does, and the kernel's own soundness is argued informally, not machine-checked.
If you find a theorem whose statement says less than its name suggests, that is
a bug we want to hear about.

## Contributing

Issues and pull requests are welcome; see [`CONTRIBUTING.md`](CONTRIBUTING.md).
Run `python3 scripts/test-suite-runner.py` for the suite runner’s failure controls without a JVM.

## License

Copyright 2026 Flexiana. Licensed under the [Apache License, Version 2.0](LICENSE).
