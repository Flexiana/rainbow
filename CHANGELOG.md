# Changelog

All notable changes to Rainbow's open core. The project follows
[Semantic Versioning](https://semver.org/).

## [Unreleased]

### Fixed
- Re-aliased inductive blocks retain every navigation alias across environment save and kernel replay.
- Chunked suite runs require a successful process exit and executed tests; invalid chunk sizes and empty resumes are refused.
- Module installers reject malformed environment results before marking dependencies installed.
- Interrupted checkpoint packing keeps complete, expandable files and supports retry; gzip writes replace files atomically.
- Reproduction recomputes rebuilt checkpoint IDs, rejecting changed content with a stale stored ID.
- Environment and checkpoint writers ignore diagnostic print limits; checkpoints can use bare filenames.
- Bundle files preserve reserved symbol aliases and complete EDN under diagnostic print settings.
- Bundles containing new inductive blocks use schema 2 with ordered, atomic block entries.
  Ordinary bundles retain schema 1; both schemas are checked, and ambiguous payloads are rejected.
- Checkpoint retries no longer reuse rejected results after transient I/O failures or insufficient budgets.
- Proof-bundle export preserves new aliases attached to proofs already present in its base.
- Verification fails when a bundle command names no files or a bundle names no claims.
  Unreadable bundles are reported individually so later files still get checked.
- Module verification checks that each advertised alias resolves to the supplied proof ID
  and that installers return declaration environments.
- The coverage inventory reads complete namespace imports, rejects pending modules and
  empty discovery, and runs in CI alongside verifier and dependency-installer regression tests.

## [1.0.0] - 2026-10-13

### Changed
- **Declarative module dependencies.** A proof module declares the modules it builds
  on as data (`deps`) and adds only its own declarations (`install`);
  `rainbow.module/install-module` installs the dependency graph once, in dependency
  order. Installing a module deep in the corpus went from over an hour (shared
  dependencies were re-installed once per path) to minutes, and every declaration id
  is unchanged. See `doc/modules.md`.
- **Every proof module is under a test.** The coverage gate re-checks every proof
  module that no other test reaches; nothing is pending.

### Verified
- Full test suite in 24 chunks: 1,875 tests, 17,953 assertions. The release gate,
  load checks for every source and test namespace, and the 15 coverage-gate
  namespaces are part of it. The coverage gate re-checks every proof module no other
  test reaches; its only axioms are the named classical ones in `set-boundary` and
  `set-union` (excluded middle, proposition extensionality), asserted per theorem.
- `lein verify --bundle` on four external proof bundles: all OK. Two tampered
  controls are rejected, one with the kernel's reason and one for schema version.
- `lein reproduce rainbow.milestones.ahof-bisection`: SAME.

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
