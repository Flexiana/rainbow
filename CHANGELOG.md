# Changelog

All notable changes to Rainbow's open core. The project follows
[Semantic Versioning](https://semver.org/).

## [1.2.0] - 2026-10-16

### Added
- **Binary bundle files** (`lein share-bundle --binary`): a shared bundle with a one-byte
  tag per node, back references as variable-length integers, constants as raw 32-byte
  hashes. `lein verify --bundle` reads binary and EDN files alike. The RH2EDIN c2
  certificate: 2,363,278 bytes plain, 15,571 shared, 5,591 binary (3,623 gzipped). The
  unpacker refuses malformed files; a sweep flipping every byte of a packed bundle never
  produces an accepted bundle with different claims.

- **Proof by reflection for natural-number ring identities**
  (`rainbow.math.nat.ring-reflect`, soundness in `ring-reflect-sound`): a goal is
  checked by normalizing both sides to Horner polynomials in the kernel; one theorem
  (`ring/identity-sound`) turns that into the proof. (a+b+c)^3: 4,753 proof nodes
  instead of 857,095 as a rewrite chain; (a+b+c)^4, which a rewrite chain cannot build
  in 6 GB, checks in about 0.4 s.
- **An LP certificate checker with its soundness theorem**
  (`rainbow.math.rational.signed.lp-certificate-reflect`): an optimality certificate is
  `lp/certificate-check-sound` applied to the instance data and `refl true`, with the
  same statement as before.

### Fixed
- Shared bundles encode `[:nat n]` literal nodes (1.1 refused bundles containing them).

### Verified
- Full test suite, 25 chunks: 1,988 tests, 44,112 assertions, 0 failures (two chunks
  re-run after a test fix and a generator fix that touched only them).
- `lein verify --bundle` on the four RH2EDIN bundles; a reflected c2 certificate in plain
  (330,141 bytes), shared (11,674) and binary (4,640) form, all OK; a binary file with one
  byte changed is refused.
- Binary format: a mutation sweep of 2,537,120 single-byte substitutions, insertions,
  deletions and multi-byte edits, none accepted with other claims.
- The nested-binder control is rejected; `lein reproduce rainbow.milestones.ahof-bisection`
  gives SAME.

## [1.1.1] - 2026-10-16

### Fixed
- The README, CONTRIBUTING, the tour and the CI trusted-base check still stated the
  1.0 kernel's 1,198 lines; they now state the 1,364 lines 1.1.0 ships (the release
  test already pinned 1,364). No code changes.

## [1.1.0] - 2026-10-16

1.0.1 was prepared but never tagged; its repairs ship here, so 1.1.0 is the release to
upgrade to from 1.0.0.

### Security
- **Kernel soundness: 1.0.0 accepts a proof of False. Upgrade.** When computing an
  inductive block's content id, 1.0.0 restarted binder numbering at every nested Pi,
  so `forall X Y : Prop, X -> X` and `forall X Y : Prop, X -> Y` received the same
  block id. Adding the second block replaced the first, and its recursor then proved
  `forall P : Prop, P` with an empty axiom set, through public kernel APIs from an
  empty environment. Binder positions are now absolute across nested Pis
  (`test/rainbow/inductive_identity_test.clj` is the regression). No shipped
  declaration depended on the defect: the default checkpoint replays to the same
  environment id as under 1.0.0, so every content id is unchanged. The repair
  shortened the kernel to 1,198 lines; see Changed for 1.1.0's trusted base.

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

### Changed
- **The kernel computes natural-number arithmetic natively: 24-123x faster on the
  RH2EDIN certificates** (c2 trailer allocation: 36.3 s -> 0.45 s; Lean 4 with
  Mathlib checks a comparable proof of the same instance in 19.6 ms). Same theorems,
  same proofs, same content ids:
  - natural-number literals `[:nat n]` stand for `succ` applied n times to `zero`; six
    reducible definitions (`algebra/nat-add`, `nat/multiply`, `nat/predecessor`,
    `nat/distance`, `nat/decide-equality`, `nat/decide-at-most`) are computed on
    closed numeral arguments (an open argument is unfolded exactly as before; argument
    evaluation never counts against the caller's reduction budget), each pinned to its definition's content id and tested against that
    definition's own unary reduction. No existing term contains a literal, and
    `kernel/normalize` still returns unary numerals (bounded by `:max-unary-nodes`).
  - substitution skips subterms with nothing to substitute, universe levels of a
    definition body are normalized once, and content-id encoding writes through one
    buffer (byte-identical, tested against the original).
  - Definitional equality is the original normal-form comparison, unchanged.
  - An independent review compared the new kernel with a frozen copy of the original
    on 25,716 assertions (native operations, malformed terms, large indices, cache
    behavior, the nested-binder control) and replayed 2,199 declarations through both
    to the same environment id. Five divergences it found were fixed before release.
  - The trusted base grows from 1,198 to 1,364 lines (`doc/trusted-base.md`).
- `lein verify --bundle` no longer re-checks each claim after the kernel has accepted
  it (twice, until now); it reports the check time per bundle.

### Added
- **Shared proof bundles** (schema 3): every distinct subterm written once and every
  constant once, by position. The RH2EDIN c2 certificate goes from 2,363,278 to 15,571
  bytes. Same declarations, same content ids, same kernel; `lein verify --bundle`
  checks both encodings and `lein share-bundle` converts. See `doc/bundles.md`.
- **`lein show`**: a theorem's statement for people, with alias names, binder names
  from the source when they provably belong to the term, decimal numerals, infix
  arithmetic, sums and lists as data, explicit elision and a legend. A view; the kernel
  term is what is checked.


### Verified
- Full test suite in 25 chunks: 1,955 tests, 43,628 assertions, 0 failures; release
  gate, load checks of every source and test namespace, and the coverage gate included.
- `lein verify --bundle` on the four RH2EDIN bundles, plain and shared: all OK, same
  claims (c2: 8.0 s plain, 8.1 s shared, end to end). Tampered bundles (an unknown
  constant, a missing schema, one price changed in a shared bundle) are all refused,
  the last by the kernel (`:kernel/type-mismatch`).
- The 2026-10-14 nested-binder control is rejected; `lein reproduce
  rainbow.milestones.ahof-bisection` gives SAME.
- Kernel review: a frozen copy of the 1.0.1 kernel as a differential oracle, 25,716
  assertions, replay of 2,199 declarations to the same environment id; the two later
  kernel follow-ups (closed arguments, separate allowance) reviewed the same way.

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
