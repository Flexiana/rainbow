# Changelog

All notable changes to Rainbow's open core. The project follows
[Semantic Versioning](https://semver.org/).

## [1.0.0-rc.2] - 2026-10-13

### Changed
- **Claims say what is proved.** The kernel classifies every theorem as a statement
  for all inputs, a definitional unfolding (true by unfolding a definition), or a
  worked instance about specific values; `lein verify` prints which. Of the 415
  algorithm proof modules, 48 prove a guarantee for all inputs; the rest prove worked
  instances or unfoldings and say so in a generated scope note. 83 module docstrings
  that presented an algorithm's classical guarantee as proved were corrected; see
  `doc/claims.md`.
- Every algorithm proof module now installs on its own (31 modules declared
  dependencies they had relied on implicitly).
- `lein verify --bundle` requires a supported `:rainbow.bundle/schema-version`, honours
  a recorded or `--reductions` budget, and names the kernel's reason for a failure.

### Added
- Coverage gate: every proof module must be reached by a test. Generated tests
  re-check every algorithm module no other test reaches.

### Known before 1.0.0
- Proof modules are installed by calling their dependencies' installers, so a module
  deep in the dependency graph re-installs shared dependencies many times (measured:
  one module, 10,343 module installs of 184 distinct). 1.0.0 replaces this with
  declarative module dependencies, installed once each in dependency order. Until
  then, the slow modules are listed in `test/rainbow/coverage/pending.edn` instead
  of being re-checked by a test; 1.0.0 empties that list.

## [1.0.0-rc.1] - 2026-10-12

First public release candidate of the open core.

### Included
- The trusted kernel (1,200 lines: `kernel`, `term`, `environment`, `canonical`),
  the elaborator, the basic tactics and the baseline proof search.
- The Level 1-3 corpus: natural numbers, rationals and signed rationals, finite
  sums, order, convexity and duality, finite matrices, Markov chains, and the
  222-algorithm Applied Higher-Order Functions catalogue.
- `lein verify`: install a module through the kernel, re-check its theorems, print
  each theorem's axioms.
- `lein verify --bundle [--reductions N]`: re-check proof bundles produced
  elsewhere, with the kernel alone.
- `lein reproduce`: rebuild a milestone checkpoint from source and compare its
  content id with the recorded one.
- The Lean 4 bridge (`foreign/lean`).
- Checkpoints store each declaration once (`artifacts/store/`).

### Release gate
`rainbow.v1-release-test` (Gates A-F: trusted kernel and replay, interactive
proving, automation loop, Lean round trip, decision services, compactness) passes.

### Known before 1.0.0
- Many catalogue modules prove worked instances of an algorithm's decision step,
  not its classical guarantee; module docstrings say which, and 1.0.0 will state
  the measured split.
- Some proof modules are reached by no test; 1.0.0 adds a coverage gate.
