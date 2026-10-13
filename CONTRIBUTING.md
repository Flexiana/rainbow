# Contributing to Rainbow

Thank you for looking. Rainbow is maintained by Flexiana; issues and pull
requests are welcome.

## Reporting a problem

The most valuable report is a theorem that says less than its name or docstring
suggests: a premise nobody needs, a statement that is trivially true, a
quantifier over the wrong thing. Open an issue with the declaration name and
what you expected it to say. A kernel soundness problem — a false statement the
kernel accepts — is the most serious bug there can be here; please report it
privately to the maintainers first (see the contact address on
[flexiana.com](https://flexiana.com/contact)).

## Changing code

- **The kernel** (`kernel.clj`, `term.clj`, `environment.clj`, `canonical.clj`)
  is pinned at 1,200 lines by a release test. A change there needs a stated
  reason and a review of what it adds to the trusted base.
- **A new theorem** goes in a module under `src/rainbow/math/` or
  `src/rainbow/algorithms/proofs/` with `theorem-specs`, `deps`, `install`,
  `extend-environment` and `theorem-ids` (see [`doc/modules.md`](doc/modules.md)),
  and a test that re-checks each declaration and asserts its
  axiom profile is empty (see any `*_test.clj` next to a module you are
  extending). `lein verify <your.namespace>` should print every theorem as
  `checked` and `axiom-free`. The coverage gate (`test/rainbow/coverage/`) fails if
  a proof module is reached by no test.
- **Name binders uniquely** in term-building helpers. A helper that binds a
  fixed name such as `'x` captures a caller's variable of the same name, and the
  failure shows up far away as a type mismatch.
- Keep the maturity vocabulary exact: a theorem about a model is Level 3, and
  no amount of testing makes it a verified program.

## Running the tests

`lein test <namespace>` for one namespace; `scripts/run-suite-chunked.sh 40` for
the whole suite in fresh JVMs (it takes hours; many tests replay large
checkpoints through the kernel).

## License

By contributing you agree that your contributions are licensed under the
Apache License, Version 2.0, as the rest of the repository is.
