# Changelog

All notable changes to Rainbow's open core. The project follows
[Semantic Versioning](https://semver.org/).

## [1.5.1] - 2026-10-30

A fix to what the LP certificate checker certifies, error messages for `lein lp-view`, and a
stack fix in the elaborator. Please upgrade if you check LP certificates.

### Fixed
- **`certify` checks the shape of what it certifies.** The lookup tables behind the LP
  certificate read the last entry for any index past the end, and the checked statement covers
  only the instance's own rows and columns. So a plan or price vector with an extra entry (for
  example the plan `[3 0 7]` for a two-column instance) was certified about its first entries,
  while the result and the `lein lp-view` page named all of them; a short vector repeated its last
  entry. `certify` and `bound` now refuse such data before any other work, with
  `:lp-certificate/shape-mismatch` naming the field, its expected and actual length. Entries must
  be exact rationals (`:lp-certificate/not-rational`; floating-point numbers were silently
  rationalized before), and `:sense` must be absent, `:maximize` or `:minimize`
  (`:lp-certificate/unknown-sense`; a misspelt sense was silently treated as maximize).
  Certificates of the right shape are certified exactly as before.
- `lein lp-view` prints one `FAIL lp-view ...` line saying what to check, and exits 1, for a
  missing or unreadable file, data that is not an instance or certificate, a shape refusal, or a
  missing `--checkpoint`, instead of a raw exception.
- The elaborator turns deeply nested terms (thousands of applications or binders) into kernel
  terms without overflowing the call stack; the translation is unchanged.
- Docstrings of five LP modules describe what each produces or checks, without a maturity
  label.

### Verified
- Generated from internal 6806b8a5. Every store id is the SHA-256 of its declaration (6,309 of
  6,309; Pro 6,323 of 6,323), the same declarations as 1.5.0.
- `lein reproduce --all` in this repository: 53 of 53 rebuilt checkpoints match their recorded
  content ids. The four milestones that need the Mathlib catalog were not rebuilt.
- In this repository, the 96 test namespaces that load the changed code passed: 416 tests, 3,868
  assertions, 0 failures, 0 errors.
- Internally, the elaborator change passed the full suite (2,333 namespaces, 6,065 tests, 391,166
  assertions, 0 failures), and the LP change passed the 206 test namespaces that load it (716
  tests, 7,218 assertions, 0 failures).
- No kernel change: the trusted base stays at 1,661 lines.

## [1.5.0] - 2026-10-29

Proof search is much faster and gains a simp-like rewriting engine. The kernel adds a lazy
conversion check to type checking. Two auditor tools arrive in the open core: `lein explore`, a
Proof Explorer page, and `lein lp-view`, together with the LP certificate checker itself, which
moves here from Rainbow Pro. The Lean exporter now handles inductive types and axioms. The trusted
base grows from 1,548 to 1,661 lines.

### Changed (trusted base)
- **Lazy conversion in type checking.** When `check*` compares an inferred type with the
  expected one, it first tries a lazy comparison: head reduction without unfolding definitions,
  congruence on equal heads, and unfolding one definition at a time. If that fails, it falls back
  to the original full-normalisation procedure, unchanged. Every lazy step is a conversion rule the
  original procedure already uses, so a lazy success means the normal forms are equal. The public
  `kernel/definitionally-equal?` still uses the original procedure.
  - Measured: a `kernel/check` that succeeds on a signed-sum step is 85-280x faster (68 ms to
    0.24 ms). A check that fails is 2.1x slower (67 ms to 142 ms), because the lazy attempt runs
    first. Lazy conversion alone does not speed up proof search, which spends its time in the
    public `definitionally-equal?`, `infer` and `normalize`; the gain is in checking and replaying
    proofs whose steps check.
  - Trusted base: 1,548 to 1,661 lines (`kernel.clj` 1,248, `term.clj` 320, `environment.clj` 48,
    `canonical.clj` 45), pinned by the release test.

### Added
- **`lein explore`: the Proof Explorer.** `lein explore <checkpoint-or-bundle> [out-dir] [--roots a,b]`
  writes a static page (data inline, opens from disk; `--offline` inlines the vendored MIT
  libraries) with the dependency graph, proof trees, axiom closures and kernel-computed example
  values for natural-number and nonnegative-rational equations. A bundle is replayed as
  `lein verify --bundle` does before anything is drawn.
- **LP certificate checker in the open core, and `lein lp-view`.** The LP optimality certificate
  checker (`rainbow.or.lp-certificate`, `certify`) moves from Rainbow Pro to the open core,
  together with what an auditor needs to check an LP result: the proof-value wire format
  (`rainbow.or.lp-certificate-wire`), the original-plan and report verifiers
  (`rainbow.or.lp-original-plan-verifier`, `rainbow.or.lp-report-verifier`), the derivation of an
  instance from named activities and resources with its `explain` (`rainbow.or.lp-model`), and the
  LP bridge proof modules (`rainbow.math.rational.signed.lp-*-bridge`). They keep the names Rainbow
  Pro 1.4.x used, so code that requires them is unchanged. `lein lp-view <instance.edn>
  <certificate.edn> [out-dir]` runs `certify` and writes the LP Certificate Viewer, a static page
  with its data inline. The verdict is the kernel's check of one instance of
  `optimization/signed-lp-optimality-certificate-on`; the page also shows every comparison that
  proof is built from, each confirmed by its own kernel check, so a refused certificate names the
  comparison that failed. Negative controls must be refused, or nothing is written.
- **Simp engine (`rainbow.simp`, search option `:native-simp?`).** An untrusted search step. Its
  rules are the environment's theorems and the local hypotheses, oriented as rewrite rules, with
  conditional rewriting, backward chaining and definitional reflexivity. A rule is used only when
  the reuse index and policy admit it, so a held-out theorem stays held out. Each rewrite is a
  Leibniz transport, and the kernel checks every result like any other step.
- **One reuse policy for every lemma.** With a reuse index, every lemma a search step takes passes
  through `reuse/admits`, including native logic steps, tautology plans and application terms, and
  so does every theorem or axiom in a returned proof. Without an explicit `:reuse-policy`, indexed
  lemmas may now use the axioms the job allows; before, reuse was silently limited to axiom-free
  lemmas.
- **Lean exporter: inductive types and axioms, with universe splitting.** A unit whose sort is
  Prop for only some universe values (List, Option, Sum, Product) is exported as copies with that
  universe set to 0 and to a successor, each with Rainbow's exact type. The earlier lifted
  `Sort (max 1 l)` workaround is removed.
- Four proving-loop benchmark goals (`loop/successor-bound`, `loop/three-transitive`,
  `loop/range-start-monotone`, `loop/range-unique`) and four lemmas now have kernel-checked, axiom-free
  proofs, checked by `proving-loop-benchmark-proofs-test`. The search found the two short goals
  from their decompositions; the two range goals needed hand-written steps where the search
  returned them blocked.

### Performance
- **Search is about 24-170x faster in states per second and 90-630x faster in attempted steps
  per second** on the five proving-loop benchmark goals. A "certainly different" pre-test uses the
  kernel's own whnf, inference runs in the goal's context, and normal forms, goal hashes and
  inferred types are memoized. This code is untrusted; every proof is still kernel-checked against
  the original goal. Goals that were already fast barely change.
- On 200 theorems sampled from the default checkpoint, each held out with everything that
  depends on it, 30 s per goal and no AI help, the search proves 171 using only the theorem's
  dependency closure (136 without simp), and 175 with the whole environment index. This measures
  Rainbow's search against itself; it is not a comparison with Lean.

### Fixed
- `lein share-bundle` with a missing or truncated input, and `lein show` with a module that
  cannot be loaded, print `FAIL ...` with what to check instead of a raw exception.
- `lein verify --checkpoint` and `lein verify --bundle` report why a checkpoint could not be
  loaded or replayed (a missing or unreadable file, or the replay category), instead of
  "did not replay: :rejected", which read like a kernel rejection.
- The generated coverage tests expected an empty axiom set for
  `logic/proof-irrelevance-from-proposition-extensionality` and `logic/prop-unit-equals-inhabited`;
  both depend on `logic/proposition-extensionality`, as the 1.4.4 entry states.
- `scripts/run-suite-chunked.sh` runs five namespaces per fresh JVM by default (one JVM with
  twenty proof environments ran out of a 5 GB heap) and closes stdin.
- `project.clj` runs tests with a 512 MB thread stack: the elaborator recurses on term depth, and
  a large signed literal overflowed the default stack.

### Changed
- The release gate reports the amount of ordinary Clojure a reader must audit instead of capping
  it (20,182 lines in this repository at 1.5.0). The trusted base keeps its exact pin.

### Verified
- Generated from internal 10e3908b. Every store id is the SHA-256 of its declaration (6,309 of
  6,309; Pro 6,323 of 6,323), the same declarations as 1.4.4.
- `lein reproduce --all` in this repository: 53 of 53 rebuilt checkpoints match their recorded
  content ids under the 1.5.0 kernel. `finite-nat`, `nat-distance`, `nat-distance-core` and
  `nat-metric-separation` were not rebuilt, because the Mathlib catalog was not present.
- This repository on its own, at the draft build before the last fixes: 1,021 test namespaces,
  2,211 tests, 62,210 assertions, 8 failures, 0 errors. The failures were the names-id test reading
  a packed checkpoint raw and two generated coverage tests expecting an empty axiom set (both under
  Fixed). After the fixes, the 24 test namespaces that load the changed code passed: 327 tests,
  2,336 assertions, 0 failures, 0 errors.
- The internal suite in full at eac0365a: 2,332 test namespaces, 6,061 tests, 391,187 assertions,
  0 failures, 0 errors. The release commit adds only the names-id test fix and the suite runner
  change; both pass.
- Lean, as a second checker: every theorem in every checkpoint of the tree this release is
  generated from (2,107 distinct theorems, including the full default checkpoint of 1,721; it
  contains this repository's checkpoints) was exported with its exact type and accepted
  by Lean 4.30.0 and by Lean 4.35.0. `#print axioms` agrees with Rainbow's axiom report on every
  one, and each of the 2,276 statements negated with their proofs kept was rejected. This checks
  the exported theorems; it is not a proof about Rainbow's kernel.
- Trusted base 1,661 lines (`kernel.clj` 1,248, `term.clj` 320, `environment.clj` 48,
  `canonical.clj` 45).

## [1.4.4] - 2026-10-27

Five fixes to what Rainbow's claims say, and a kernel change that makes it accept proofs it
wrongly refused. None of the five lets the kernel accept an ill-typed term; each could make a
claim about a checked theorem (what a name refers to, which logic it uses, which axioms it
depends on) say something false. Please upgrade if you rely on names, profiles or axiom reports.
The trusted base grows from 1,471 to 1,548 lines.

### Security
- **A checkpoint could be edited to change what its names refer to (A1).** The environment id
  hashes declaration and block ids only, and a checkpoint id is a content hash anyone can
  recompute. Swapping the aliases of `algebra/nat-add` and `nat/multiply` in a stored checkpoint
  gives a checkpoint that replays to the same environment id, in which `algebra/nat-add` applied
  to 2 and 3 computes 6, so a theorem stating 2 + 3 = 6 by that name is accepted with no axioms. Replay now also reports a **names id**, the content id of the
  name-to-declaration bindings (`rainbow.persistence/names-id`); `lein verify --checkpoint` prints
  both ids. Proof bundles record the base's names id and `lein verify --bundle` refuses a base
  whose names differ; a bundle made before 1.4.4 records none and is reported as "names not
  pinned". The environment id is unchanged, so every published environment id stays valid. A
  claim made by name should cite both ids.
- **A logic profile trusted names and provenance, not the axiom (A2).** An axiom of type
  `forall P : Prop, P` declared with provenance `:classical`, or merely given the alias
  `logic/excluded-middle`, was classified as excluded middle, so a theorem using it was reported
  under the `:classical` profile. `rainbow.math.profile/principle-of` now accepts a principle only
  when the axiom's content id is that principle's own declaration id.
- **Members of an inductive type reported no axioms (A3).** A constructor or recursor whose type
  mentions an axiom (a field of a postulated type) reported an empty axiom set, so theorems using
  it could be reported axiom-free. `add-inductive-block` now gives each member the axioms of the
  constants in its type. Content ids are unchanged. No inductive type in this repository mentions
  an axiom, so no reported axiom set here changes.
- **A shared definition could be replaced silently (A4).**
  `rainbow.math.milestone-support/extend-with-shared` compared only the type and universes of a
  declaration already installed under the same name, so a definition with a different body was
  kept without notice, against its docstring. A definition under an existing name must now have
  the same kind and a definitionally equal body, or installation throws "one alias, two
  definitions". Modules that install a declaration only when its name is missing still compare
  names only; that is unchanged in this release.
- **An unknown name was classified as constructive (A5).**
  `rainbow.math.profile/classify-declaration` now reports `:unknown` for a name the environment
  does not know, outside every profile.

### Who is affected
- Whether a term type-checks: not affected by any of the five.
- Claims read by name from a checkpoint or bundle you did not build yourself: check the names
  id as well as the environment id.
- A theorem reported `axiom-free` that uses an inductive type declared outside this repository
  whose fields mention an axiom: re-check its axiom set with 1.4.4.
- A theorem reported under a profile: re-classify it with 1.4.4 if any axiom in its environment
  came from outside this repository.

### Changed
- **Universe levels are compared by value.** Definitional equality compared normal forms
  exactly, and the level normal form is not complete, so `max (succ u) u` and `succ u`, or the
  two groupings of a three-way `max`, were different and correct proofs using them were refused.
  The kernel now treats two levels as equal when they agree under every assignment
  (`rainbow.term/level-equivalent?`): a level without `imax` has a canonical shape, and each
  parameter under an `imax`'s second argument is split into 0 and a successor. Level normal forms
  and every content id are unchanged. Beyond 12 such parameters in one comparison the kernel
  falls back to comparing normal forms, as before.

### Added
- **Proof irrelevance is a theorem of propositional extensionality.**
  `logic/proof-irrelevance-from-proposition-extensionality` (`rainbow.math.logic.proof-irrelevance`)
  has exactly the statement of the axiom `logic/proof-irrelevance`, and its kernel axiom set is
  exactly `#{logic/proposition-extensionality}`: no excluded middle, choice or proof irrelevance.
  The axiom stays declared; a proof that needs only proof irrelevance can now cite this theorem
  and depend on propositional extensionality instead.

### Fixed
- A spec without `:universes` is installed with no universe parameters
  (`milestone-support/add-spec` passed `nil`, which the kernel rejected).

### Verified
- Generated from internal 63163336. Every store id is the SHA-256 of its declaration (6,309 of
  6,309; Pro 6,323 of 6,323), the same declarations as 1.4.3.
- `lein reproduce --all` in this repository: 53 of 53 rebuilt checkpoints match their recorded
  content ids. `finite-nat`, `nat-distance`, `nat-distance-core` and `nat-metric-separation`
  were not rebuilt, because the Mathlib catalog was not present.
- This repository on its own: 987 test namespaces, 2,051 tests, 51,381 assertions, 0 failures,
  0 errors.
- The internal suite in full at abd805e4: 2,313 test namespaces, 6,013 tests, 380,879 assertions,
  0 failures, 0 errors. The release commit 63163336 changes one test only (`names-id-test` now
  reads its checkpoint through the checkpoint reader, as published checkpoints are stored packed);
  it passes in both trees.
- "No inductive type in this repository mentions an axiom" was checked directly: all 256
  checkpoints replayed under 1.4.4, and none of their 11,950 inductive types, constructors and
  recursors has a non-empty axiom set.
- Trusted base 1,548 lines: `term.clj` 254 -> 320 (level equivalence), `kernel.clj` 1,124 -> 1,135
  (members' axioms, level comparison); `environment.clj` and `canonical.clj` unchanged.

## [1.4.3] - 2026-10-25

`lein reproduce` works again after 1.4.2's checkpoint migration, and proof search can build its
reuse index with less memory. No kernel change; the trusted base is unchanged at 1,471 lines.

### Fixed
- **`lein reproduce` reported DIFF or failed for migrated milestones** (for example
  `rainbow.milestones.or-contraction` and `rainbow.milestones.ahof-bisection`). Three causes:
  - A saved environment wrote `:rainbow/level-requirements`, which the 1.4.2 kernel derives
    whenever it admits a declaration and keeps out of every declaration id. A rebuilt checkpoint
    therefore carried it, and the migrated checkpoints did not. It is no longer written. Replay
    recomputes it, so nothing the kernel checks changes, and no stored checkpoint changes either.
  - `:retracted-mappings`, which 1.4.2 added to the migrated checkpoints, was dropped when a
    checkpoint was loaded and so was missing from every rebuild. It is now carried forward.
  - Milestone precommits name their input checkpoint by id, and 1.4.2 changed 249 checkpoint
    ids. Precommits are not edited after the fact. Instead
    `artifacts/migrations/1.4.2-checkpoint-ids.edn` records each old and new id, and a
    precommitted id is accepted only for the checkpoint the record says it became
    (`rainbow.checkpoint/same-input-checkpoint?`). Reports written before 1.4.2 still name the
    old ids; the same record maps them.
- **`rainbow.milestones.vector-equivalence-laws` did not reproduce, in 1.4.1 and earlier too.**
  Its checkpoint had been recorded with `vector/equivalent` as it stood before the 2026-08-21
  fix that made the relation length-sensitive; before that fix `[]` was equivalent to `[x]`. Its
  precommit already named the length-sensitive relation. It was rerun from source and proves the
  same four targets with the same search (none at baseline, four with the new lemmas, 8 search
  states). `rainbow.milestones.nnrat-additive-reassociation`, which builds on it, was rerun as
  well and proves the same three targets. `artifacts/migrations/1.4.3-checkpoint-ids.edn`
  records both id changes, so the precommits are again left as they were.
- **`lein reproduce` stopped with "Wrong number of args" on milestones whose `run` takes more
  than the input checkpoint**: `finite-nat`, `nat-distance`, `nat-distance-core` and
  `nat-metric-separation` also take the Mathlib catalog. It now passes each argument its
  `default-` value. When an input file is missing, which on a fresh checkout means the
  catalog that `scripts/export-mathlib-catalog.sh` builds from Mathlib v4.30.0, the milestone is
  listed as `NEEDS` and not rebuilt. A missing input does not fail the command; a `DIFF` or
  `FAIL` still does.
- A saved environment containing a natural-number literal could not be replayed: the
  persistence schema did not accept `:nat` terms.
- The reuse index could not be built for a type containing a natural-number literal.

### Changed
- `rainbow.reuse/build-index` takes `:incremental? true`. It hashes each normalized type by
  streaming its encoding into the digest (`rainbow.canonical-stream`, new, outside the trusted
  base) instead of building the encoding as one string, and renames universe parameters once per
  shared subterm instead of once per occurrence. The index is the same either way, with the same
  `:reuse/id`; a test builds both and compares them. The default is unchanged.
- `rainbow.search/prove` takes a `:progress!` callback, called with the completed expansion
  counters and the current search state. It reports progress only; a proof is still accepted
  only after reconstruction and kernel checking.

### Verified
- Generated from internal 5e1af921. Every store id is the SHA-256 of its declaration (6,309 of
  6,309; Pro 6,323 of 6,323). That is three fewer than 1.4.2: the eight superseded `vector/*`
  declarations are gone and five are new; the rerun's other declarations were already stored.
- `lein reproduce --all` in this repository: 53 of 53 rebuilt checkpoints match their recorded
  content ids. `finite-nat`, `nat-distance`, `nat-distance-core` and `nat-metric-separation`
  were not rebuilt, because the Mathlib catalog was not present.
- This repository on its own: 974 test namespaces, 2,030 tests, 47,278 assertions, 0 failures,
  0 errors.
- The internal suite was not rerun in full. The 49 internal test namespaces that load the changed
  code passed: 168 tests, 4,036 assertions, 0 failures, 0 errors. Of the 89 internal milestones,
  53 rebuild to their recorded ids and 36 need the Mathlib catalog (rebuilt at the preceding
  commit f01283ac, the two rerun milestones again at 5e1af921).
- No kernel change: `kernel.clj` is identical to 1.4.2, and the trusted base is 1,471 lines.

## [1.4.2] - 2026-10-25

Two soundness fixes in the kernel, both about inductive types. Before them, a user-declared
inductive type, or a proof using the proof-irrelevance axiom, could derive False. Please upgrade.

### Security
- **Constructor fields were not checked against the inductive type's universe.**
  `add-inductive-block` checked that each generated type was well typed, but never compared a
  field's universe with the type's own. A type could contain its own universe (`U : Sort 1`
  with a constructor `Sort 1 -> U` was accepted), and from that False is derivable without
  axioms (Girard's paradox; we checked the ingredients, not the full proof term). Every
  non-recursive constructor field must now live in a universe at most the type's, for every
  value of the universe parameters. There is no exception for propositions, so an inductive
  proposition with a field in a larger universe is refused. Every inductive type in this
  repository passes the new check.
- **Large elimination from propositions.** `data/Sum`, `data/Option`, `data/List` and
  `data/Product` are propositions when their universe arguments are 0, and their recursors
  still eliminated into any universe. Without axioms this is believed consistent; with proof
  irrelevance it is not, and 1.4.1 accepted a proof of False under the `:proof-irrelevant`
  profile. Now a recursor of a type with two or more constructors can eliminate into a
  universe above Prop only when the type is not a proposition. Where that depends on
  universe parameters, the requirement is recorded on the declaration and checked wherever
  it is instantiated, so definitions built on it inherit it.

### Who is affected
- An axiom-free theorem (`kernel/axioms` returns `#{}`) that uses only this repository's
  inductive types: not affected. The first issue needs an ill-formed type; the second needs
  the proof-irrelevance axiom.
- A theorem that uses an inductive type declared elsewhere: re-check it with 1.4.2.
- A theorem checked by 1.4.1 or earlier under `:proof-irrelevant`, `:mathlib-logic` or
  `:mathlib-complete-logic`, and probably `:classical` (excluded middle with an impredicative
  Prop implies proof irrelevance; we have not built that proof): that kernel's acceptance did
  not establish it. Re-check it with 1.4.2.

### Removed
- `type/finite-proposition` (`rainbow.math.finite.subtype`), which needed large elimination from
  a proposition, with the Mathlib reproof of `instFiniteProp` that used it and that reproof's
  mapping record: the store holds 6,312 declarations, 3 fewer than 1.4.1. 249 of the 256
  checkpoints contained them and are rebuilt without them, so their ids change; a checkpoint
  that mapped `instFiniteProp` keeps the mapping under `:retracted-mappings` with the reason.
  The other 7 checkpoints are unchanged. Both declarations relied on the proof-irrelevance
  axiom, so no axiom-free theorem is lost.

### Corrected
- 1.4.0 headed its MILP work "Proved MILP certificates" and said every week of 2023 "was
  proved optimal". The tree checker's soundness theorem is stated and not proved (the same
  entry said so), so what holds is weaker: 52 of 52 weekly certificates were accepted by a
  checker that is tested, not proved. That is below Level 4 (`doc/maturity-levels.md`). The same applies to the sparse LP
  checker it rests on.

### Verified
- Generated from internal 8bdabda2. Since the commit the full suite was run on (4d2b07f9), only
  documentation and one test changed; that test (`day77_test`) now reads checkpoints without a
  private helper and passes (2 tests, 15 assertions). Every store id is the SHA-256 of its
  declaration (6,312 of 6,312; Pro 6,326 of 6,326).
- The internal suite, which includes everything in this repository and in Rainbow Pro: 2,304
  test namespaces, 5,974 tests, 373,656 assertions, 0 failures, 0 errors.
- This repository on its own: 973 test namespaces, 2,022 tests, 44,229 assertions, 0 failures,
  0 errors.
- Two new kernel tests refuse each counterexample: a type containing its own universe, and the
  1.4.1 proof of False under `:proof-irrelevant`.

## [1.4.1] - 2026-10-21

Fixes to Rainbow Pro's test suite, found by running all of it against 1.4.0. Every one of these
also failed in 1.3.0. This core's code is unchanged.

### Fixed in Rainbow Pro 1.4.1
- `finite-algebra-test` did not compile ("No such var: finite/exact-runtime-examples"). The open
  core's `rainbow.algebra.finite` leaves out its code-generator demo, which needs the Pro
  compiler; the demo, the report and the command line now live in Pro as
  `rainbow.algebra.finite-report`, and the test uses them there.
- `clojure-tabu-program-family-test`: a test parameter was named `fn`, which the code
  generator refuses as a reserved name (2 errors); renamed.
- `clojure-geometric-horizon-test` pinned the printed form of the generated code, which no
  longer matched; it now checks the generated form itself (ten multiplications by 1/2, no
  iteration) and runs it on five inputs.
- `primitives-test` gave the kernel a budget of 1,000 steps to provoke an out-of-budget case,
  which native arithmetic now finishes within (3 failures); it now uses a budget of 0.
- `stroke-test`: the day-15 corpus report's id depended on the heap size of the JVM that made
  it, so a fresh JVM reported a different id. The corpus fixture now pins its memory profile,
  and a new test checks that the host's heap size no longer changes the controller.

### Verified
- Generated from internal b90e9040 (1.4.0's 9c5c9fcc plus the four test fixes). Against 1.4.0,
  this core changes only in its version and this file, and Rainbow Pro only in the files named
  above; the store and every checkpoint are byte-identical to 1.4.0, and every store id is the
  SHA-256 of its declaration (6,315 of 6,315; Pro 6,329 of 6,329).
- Rainbow Pro, against this core in a sibling layout, each of the five tests on its own: 32
  tests, 853 assertions, 0 failures, 0 errors. With 1.4.0's run, every Pro test namespace
  has now passed against 1.4.x (1,354 with tests): the 232 checked for 1.4.0, the 1,110 that
  passed in a run of all the others, the 7 that run did not reach (run separately) and the 5
  fixed here.

## [1.4.0] - 2026-10-19

This core gains 27 modules of mathematics that Pro's Level-3 certificate readings rest on;
the kernel is unchanged. This release accompanies Rainbow Pro 1.4.0.

### Added to this core
- `rainbow.math.sums` (23 modules) and `rainbow.math.lemmas` (4): LP Farkas and ray
  lemmas, bounds for LP certificates with row and column bounds, Hungarian and
  Gilmore-Gomory pricing bounds, and the indicator, one-hot and predicate-bridge lemmas
  that tie a checker's sums to the predicate it claims (admissions, budgeted protection,
  earliest schedules, Pareto masks, period usage and more). Native and axiom-free; each is
  installed by the coverage tests.

### In Rainbow Pro 1.4.0
- **Proved MILP certificates.** A branch-and-bound tree checker as one loop program: an
  integral, feasible incumbent; per node a box of column bounds, each child containing its
  parent's box cut by its side of a split on an integer column; per leaf an exact LP dual
  bound or a Farkas proof of infeasibility; and the claimed gap. It rests on a sparse LP
  certificate checker (CSR/CSC rows and columns, safe dual bound), which checks a
  22,940 x 17,572 plant LP in 3-4 s. On an e-methanol plant's week-ahead unit commitment
  (electrolyser, hydrogen tank, methanol loop with turndown and start-up costs; 674 x 840,
  168 binaries), every week of 2023 was proved optimal to within 1e-6 relative: 52 of 52
  certificates accepted, a gap smaller by 1e-6 refused for all 52, median check 0.64 s
  (at most 45 s). The soundness theorem for the tree checker is stated, not yet proved.
- **Loop language v2**: index tables read from the parameters (`clj/Index2`,
  `clj/LoopExpr2`), so a checker can compare indices and read sparse structures.
- **Loop port**: 918 of 986 program families translate to loop programs, kernel-checked per
  shape; `deploy-loop` runs a ported family at any shape. Generic check and sum loops,
  grids and the a1c port carry proved denotations.
- **Level-3 claims**: 24 more claims proved for the families' certificate readings (stable
  matching and roommates, admissions, Pareto efficiency, EVPI, Holt, Wardrop, RCPSP,
  job shop, unit commitment, lot sizing, multicommodity flow, routing, Max-Cut local
  optimality, Hall violators and others). Statements that overclaimed are corrected:
  Wagner-Whitin's "optimal over all production schedules" fails with zero demand (a
  counterexample is kernel-checked; the claim stays open), the Max-Cut claim states the
  data assumption it does not check. 450 claims that only cite where a formula comes from
  are recorded as documented assumptions with their citation, never as proved. Open
  correctness claims: 943 in 1.3.0 -> 624.
- **Audit**: a manifest that declares a raised kernel reduction budget is re-checked at it
  (it was re-checked at the default, so budget exhaustion was reported as a failure).

### Fixed in Rainbow Pro 1.4.0
- When a module is split into a public mathematics half and a Pro half, the release build
  pointed every Pro module that depended on it at the public half, even when it used the
  Pro half. In Pro 1.3.0 and 1.3.1 (the same source), 5 of the 147 such modules therefore
  failed to install on their own: on the d63 checkpoint, `rainbow.module/install-module`
  stops with an unknown constant (`clj/expr-sum`, `clj/Expr` or `clj/all-at-most`) for
  `clojure-forward-iteration-program`, `clojure-newsvendor-program-family`,
  `clojure-product-combinator`, `clojure-two-opt-program-family` and
  `expr-sum-arule-readings`. The test suite passed regardless; earlier releases were not
  checked. 1.4.0 gives the 152 Pro modules that depend on a split module their Pro half
  back, and all 152 install on their own.
- Five Pro tests reach a private var as `#'ns/var` in a namespace they did not require, so
  they compiled only after another test had loaded it; `expr-sum-benders-cut-test` run on
  its own did not compile (1.3.0: "Unable to resolve var"). The release build now adds the
  require to every such test, and each of the five passes on its own.
- The same defect in Pro tests: a test that built its environment with a split module now
  built it with the public half alone, so the Pro half's theorems were unknown constants.
  `expr-sum-mmck-unique-test` failed in 1.3.0 (1 failure, 2 errors), and with it
  `mmck-unique-independent-review-test`. Six Pro tests now build their environment with the
  Pro half; each passes on its own, as does the review test.

### Verified
- Generated from internal 9c5c9fcc.
- This core: the CI steps (trusted base 1,364 lines, unchanged; suite-runner controls, 4
  tests; kernel, 14 tests, 130 assertions; verifier and coverage guards, 40 tests, 137
  assertions; the tour's three modules re-checked, OK), the release and bundle tests (19
  tests, 82 assertions) and the coverage parts 8-15, which install the new modules (146
  tests, 946 assertions), 0 failures.
- The 27 new modules: `lein verify` reports each OK. It lists the theorems of the 4
  `rainbow.math.lemmas` modules (7, all for all inputs); the 23 `rainbow.math.sums` modules
  export no theorem list, so it reports them as installed, which kernel-checks every lemma
  they add. Every declaration each one adds, installed on its own, is axiom-free; the same
  check reports axioms for 603 of the 2,268 declarations already in the base checkpoint.
- The store and checkpoints hold the same values as 1.3.1 (256 of 256 checkpoints and the
  store decompress to identical text; Pro 272 of 272), and every store id is the SHA-256 of
  its declaration (6,315 of 6,315; Pro 6,329 of 6,329).
- Rainbow Pro, run against this core in a sibling layout: the 58 new test namespaces (206
  tests, 4,733 assertions); the 170 existing namespaces that reference a module changed in
  1.4.0 (169 pass; the other is a helper with no tests; namespaces that ran out of heap in a
  shared JVM were re-run in a fresh one); and the eleven tests changed by the fixes above,
  each on its own. 0 failures, 0 errors. Every Pro module that depends on a split module
  (152) installs on its own on the d63 checkpoint. The rest of the Pro suite, whose tests and
  modules are unchanged since 1.3.1, was not re-run for this release.

## [1.3.1] - 2026-10-19

Documentation corrections from an audit of every published claim against the repository,
and a repacked checkpoint store. No changes to the kernel, the code, or any checked value.

### Fixed
- **Store ids are now the SHA-256 of what the store holds.** In 1.1.0-1.3.0, 3,314 of the
  6,315 declarations in `artifacts/store/declarations.edn.gz` (Pro: 3,314 of 6,329) were
  filed under the hash of an earlier printing of the same value (Clojure's `#:rainbow{...}`
  namespace-map syntax, used when they were first packed), while the store prints them
  without it; the release build's pack cache carried the old ids forward. Lookups and checks
  were unaffected, since a reference resolves by its id, but those ids were not content ids
  of the stored text, as "content-addressed" in the README says. 1.3.1 repacks from scratch:
  every id is the SHA-256 of its declaration as stored (6,315 of 6,315; Pro 6,329 of 6,329).
  All 256 checkpoint files (Pro: 272) change their references accordingly; each expands to a
  value equal to its 1.3.0 value, and the declarations are the same set.
- The README and `doc/claims.md` described two kinds of statement; `lein verify` has
  printed three since 1.1 (for all inputs, definitional unfoldings, worked instances). The
  sample outputs now match what the command prints, and the README says that modules
  outside the 48 may unfold definitions as well as check worked instances.
- The classification of theorems is done by `rainbow.main` from the kernel's type
  inference, not by the kernel; the README and `doc/claims.md` now say so.
- "The corpus's theorems report axiom-free" and "the tests assert an empty profile": eight
  theorems in `set_boundary.clj` and `set_union.clj` use classical axioms (as 1.0.0's notes
  said); README, `doc/claims.md` and `doc/trusted-base.md` now say which.
- The README's suite size (about 1,600 tests / 16,000 assertions) is now about 2,000 / 44,000.
- `doc/tour.md` still gave the 1.0 kernel's 915 lines for `kernel.clj`; it is 1,017.
- The 1.3.0 entry understated the old RH2EDIN bundle sizes (0.6-3.0 MB as published, not
  0.35-1.9 MB); the 1.1.1 entry called 1,198 lines the 1.0 kernel (1.0.0 had 1,200; 1,198
  was 1.0.1).

### Verified
- Generated from internal e934fb61, as 1.3.0 was. Source, tests and scripts are
  byte-identical to 1.3.0 in both repositories; besides the documentation, only the version,
  the store and the checkpoint references differ.
- The store: every id is the SHA-256 of its stored declaration (6,315 of 6,315; Pro 6,329 of
  6,329), checked by the release build, which now refuses a store with any other id; the same
  check reports 3,314 mismatches on 1.3.0. Every checkpoint, expanded, equals its 1.3.0
  expansion (256 of 256; Pro 272 of 272), and both stores hold the same declarations as 1.3.0.
- This core: the CI steps (trusted base 1,364 lines; suite-runner controls, 4 tests; kernel,
  14 tests, 130 assertions; verifier and coverage guards, 40 tests, 137 assertions; the
  tour's three modules re-checked, OK) and the release and bundle tests (19 tests, 82
  assertions), 0 failures.
- Rainbow Pro: the release, cache, LP-gap and round-robin family tests, which replay
  checkpoints through the repacked store: 11 tests, 238 assertions, 0 failures.

## [1.3.0] - 2026-10-16

The open core's code is unchanged; this release accompanies Rainbow Pro 1.3.0, whose
output it checks.

### Checked by this core
- **Smaller LP optimality bundles.** Pro 1.3's certificate generator writes instance data
  with native numerals and, optionally, as balanced lookup trees, and proves the
  certificate by reflection. The four RH2EDIN bundles went from 0.6-3.0 MB (as previously published; c2 2.36 MB) to 6.7-8.5 KB
  (shared EDN) or 3.3-3.8 KB (binary). They check with this core, and with 1.2.0, in
  12-30 s each, axiom-free.

### In Rainbow Pro 1.3.0
- **Programs whose size does not grow with the instance**: a loop language beside
  `clj/Expr` (slots read at computed indices, loops counted by shape parameters), a
  printer that emits one Clojure function per program, a decoder that reads the printed
  text back and has the kernel confirm it is the program, and a proof that the embedding
  of `clj/Expr` preserves meaning. The graph coloring checker as one loop program is
  proved equal to the coloring family's verdict for every number of vertices and colors
  and every store, so the family's soundness and completeness carry over; it checks
  252,000 inputs in about 0.3 s, where the straight-line program stopped compiling near
  600 (JVM method size).
- **Level-3 optimality as emitted code**: assignment and closed-tour (TSP) optima by
  exhaustive permutation coverage, and unit and weighted knapsack subset optima.
- **LP certificate options**: `{:table :binary}` lookup trees (40x40 random LPs certify in
  123 s instead of 228 s; 60x60 in 457 s, where linear tables ran out of memory).

### Verified
- Generated from internal e934fb61. Rainbow Pro: every source namespace loads (7 chunks,
  0 failures); the loop-language, loop-coloring, decoder, loop-proof, Level-3 optimality,
  LP certificate (literals, binary tables, reflection, epsilon verifier) and coloring
  family tests: 72 tests, 2,042 assertions, 0 failures.
- This core: the release gate and binary-bundle tests, 13 tests, 53 assertions, 0
  failures; its code is byte-identical to 1.2.0 apart from the version.
- The four RH2EDIN bundles from Pro 1.3 check with `lein verify --bundle` (OK,
  axiom-free); a copy with one numeral changed is rejected.

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
  1.0.1 kernel's 1,198 lines (1.0.0 had 1,200); they now state the 1,364 lines 1.1.0 ships (the release
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
