# The corpus

Every proof module in the open core: 1185 modules, grouped by folder. Each line links to the source and
quotes the first sentence of its docstring. Re-check any of them with `lein verify <namespace>`.
This file is generated from the source tree; do not edit it by hand.

## Foundations (`src/rainbow/math/`, 8)

| namespace | |
|---|---|
| [`rainbow.math.checks`](../src/rainbow/math/checks.clj) | General lemmas: checks. |
| [`rainbow.math.constructive-unique-fixed-point`](../src/rainbow/math/constructive_unique_fixed_point.clj) | Constructive existence and support-relative uniqueness for strict Nat contractions. |
| [`rainbow.math.monte-carlo-estimation`](../src/rainbow/math/monte_carlo_estimation.clj) | Direct Monte Carlo estimation of a failure probability. |
| [`rainbow.math.nonnegative-rational`](../src/rainbow/math/nonnegative_rational.clj) | Nonnegative rationals as proof data: numerator plus denominator predecessor. |
| [`rainbow.math.or-foundation`](../src/rainbow/math/or_foundation.clj) | Small reusable proof-data laws shared by OR representations. |
| [`rainbow.math.prelude`](../src/rainbow/math/prelude.clj) | Native, data-oriented concepts selected from corpus nativeization failures. |
| [`rainbow.math.real-analysis-foundation`](../src/rainbow/math/real_analysis_foundation.clj) | FIRST brick of the real-analysis layer -- the gating foundation for frontier OR (convergence rates, GP regret, MDP contraction, LP duality all live over the reals). |
| [`rainbow.math.temporal-difference`](../src/rainbow/math/temporal_difference.clj) | Bounded temporal-difference (Q-learning) updates over signed rationals. |

## Analysis (`src/rainbow/math/analysis/`, 6)

| namespace | |
|---|---|
| [`rainbow.math.analysis.geometric-convergence`](../src/rainbow/math/analysis/geometric_convergence.clj) | Worked geometric convergence: the contraction distance provably reaches below each accuracy threshold at a computable step. |
| [`rainbow.math.analysis.geometric-decay`](../src/rainbow/math/analysis/geometric_decay.clj) | The geometric contraction bound -- the analysis entry point for value-iteration convergence. |
| [`rainbow.math.analysis.geometric-denominator`](../src/rainbow/math/analysis/geometric_denominator.clj) | The denominator half of the geometric-sequence closed form: denominator (seq d0 N) = denominator d0 * 2^N for every N, completing (with geometric/seq-numerator-invariant) the closed form seq d0 N = num(d0) / (den(d0) * 2 |
| [`rainbow.math.analysis.geometric-modulus`](../src/rainbow/math/analysis/geometric_modulus.clj) | The geometric-convergence MODULUS -- the last ingredient of the general forall-epsilon rational convergence theorem. |
| [`rainbow.math.analysis.geometric-sequence`](../src/rainbow/math/analysis/geometric_sequence.clj) | The geometric contraction sequence as a native recursive function and its general (forall-n) step monotonicity -- the sequence-level consequence of the halving-monotonicity keystone (nnrat/half-le-self). |
| [`rainbow.math.analysis.geometric-threshold`](../src/rainbow/math/analysis/geometric_threshold.clj) | The first fully-general-over-n convergence statement for the geometric contraction: for the worked start distance d0 = 8 and threshold eps = 1, the distance is at most 1 at EVERY step from the modulus 3 onward: forall n. |

## Finite types, distributions and Markov chains (`src/rainbow/math/finite/`, 122)

| namespace | |
|---|---|
| [`rainbow.math.finite.async-value-iteration`](../src/rainbow/math/finite/async_value_iteration.clj) | Asynchronous (Gauss-Seidel) finite Bellman value iteration. |
| [`rainbow.math.finite.bellman`](../src/rainbow/math/finite/bellman.clj) | Exact scaled finite transition rows and fixed-policy Bellman numerators. |
| [`rainbow.math.finite.bellman-backup-contraction`](../src/rainbow/math/finite/bellman_backup_contraction.clj) | Discount-scaled contraction of finite NNRAT Bellman backups and T*. |
| [`rainbow.math.finite.bellman-fixed-point-uniqueness`](../src/rainbow/math/finite/bellman_fixed_point_uniqueness.clj) | Constructive uniqueness of exact finite NNRAT Bellman optimality fixed points. |
| [`rainbow.math.finite.bellman-greedy-policy-optimal`](../src/rainbow/math/finite/bellman_greedy_policy_optimal.clj) | Fully concrete greedy-policy extraction for exact finite NNRAT Bellman models. |
| [`rainbow.math.finite.bellman-iterate-monotone`](../src/rainbow/math/finite/bellman_iterate_monotone.clj) | A post-fixed nnrat value function lies below every finite iterate of the Bellman optimality operator. |
| [`rainbow.math.finite.bellman-monotone`](../src/rainbow/math/finite/bellman_monotone.clj) | Monotonicity of finite nnrat expectations, Bellman action backups, and the Bellman optimality operator. |
| [`rainbow.math.finite.bellman-optimal-contraction`](../src/rainbow/math/finite/bellman_optimal_contraction.clj) | Finite-argmax nonexpansiveness for the NNRAT Bellman optimality layer. |
| [`rainbow.math.finite.bellman-optimality`](../src/rainbow/math/finite/bellman_optimality.clj) | Bellman optimality, operator level: the optimal (greedy / max-over-actions) Bellman backup dominates every fixed-policy backup. |
| [`rainbow.math.finite.bellman-policy-residual-certificate`](../src/rainbow/math/finite/bellman_policy_residual_certificate.clj) | Residual certificates and uniqueness for exact finite fixed-policy Bellman operators. |
| [`rainbow.math.finite.bellman-residual-certificate`](../src/rainbow/math/finite/bellman_residual_certificate.clj) | A posteriori certificates for exact finite NNRAT Bellman solvers. |
| [`rainbow.math.finite.bellman-signed-action-backup`](../src/rainbow/math/finite/bellman_signed_action_backup.clj) | Concrete signed Bellman action backups and their additive contraction. |
| [`rainbow.math.finite.bellman-signed-approximate-optimality`](../src/rainbow/math/finite/bellman_signed_approximate_optimality.clj) | Constructive approximate fixed points of signed Bellman optimality. |
| [`rainbow.math.finite.bellman-signed-approximate-optimality-generic`](../src/rainbow/math/finite/bellman_signed_approximate_optimality_generic.clj) | Approximate fixed points for a certified finite signed Bellman operator. |
| [`rainbow.math.finite.bellman-signed-fixed-point-uniqueness`](../src/rainbow/math/finite/bellman_signed_fixed_point_uniqueness.clj) | Uniqueness of signed Bellman optimality fixed points. |
| [`rainbow.math.finite.bellman-signed-greedy-policy`](../src/rainbow/math/finite/bellman_signed_greedy_policy.clj) | Greedy policy extraction from a signed Bellman fixed point. |
| [`rainbow.math.finite.bellman-signed-operator-fixed-point-convergence`](../src/rainbow/math/finite/bellman_signed_operator_fixed_point_convergence.clj) | Fixed-point convergence of the low-arity signed operator iterator. |
| [`rainbow.math.finite.bellman-signed-optimal-contraction`](../src/rainbow/math/finite/bellman_signed_optimal_contraction.clj) | Signed finite Bellman optimality inherits action-backup contraction. |
| [`rainbow.math.finite.bellman-signed-optimality`](../src/rainbow/math/finite/bellman_signed_optimality.clj) | Generic finite Bellman optimality over exact signed-rational action scores. |
| [`rainbow.math.finite.bellman-signed-policy`](../src/rainbow/math/finite/bellman_signed_policy.clj) | Signed-reward fixed-policy Bellman certificates in finite matrix form. |
| [`rainbow.math.finite.bellman-signed-policy-approximate-fixed-point`](../src/rainbow/math/finite/bellman_signed_policy_approximate_fixed_point.clj) | Constructive approximate fixed points for finite signed policy evaluation. |
| [`rainbow.math.finite.bellman-signed-policy-dominance`](../src/rainbow/math/finite/bellman_signed_policy_dominance.clj) | Dominance of admissible signed policy values by Bellman optimality. |
| [`rainbow.math.finite.bellman-signed-policy-optimal`](../src/rainbow/math/finite/bellman_signed_policy_optimal.clj) | Concrete signed greedy-policy optimality for finite Bellman models. |
| [`rainbow.math.finite.bellman-signed-policy-sensitivity`](../src/rainbow/math/finite/bellman_signed_policy_sensitivity.clj) | Robustness of signed fixed-policy Bellman evaluations under model drift. |
| [`rainbow.math.finite.bellman-signed-residual-certificate`](../src/rainbow/math/finite/bellman_signed_residual_certificate.clj) | A posteriori residual certificates for signed Bellman optimality. |
| [`rainbow.math.finite.bellman-signed-transition-approximate-optimality`](../src/rainbow/math/finite/bellman_signed_transition_approximate_optimality.clj) | Constructive approximate optimality for normalized finite signed MDPs. |
| [`rainbow.math.finite.bellman-signed-transition-bridge`](../src/rainbow/math/finite/bellman_signed_transition_bridge.clj) | Embed ordinary nonnegative transition kernels into signed Bellman proofs. |
| [`rainbow.math.finite.bellman-signed-transition-operator`](../src/rainbow/math/finite/bellman_signed_transition_operator.clj) | Named concrete signed Bellman operator over ordinary nnrat transitions. |
| [`rainbow.math.finite.bellman-signed-value-iteration`](../src/rainbow/math/finite/bellman_signed_value_iteration.clj) | Finite-horizon signed Bellman value-iteration envelopes. |
| [`rainbow.math.finite.bellman-signed-value-iteration-converges`](../src/rainbow/math/finite/bellman_signed_value_iteration_converges.clj) | Rate-null convergence certificate for signed Bellman value iteration. |
| [`rainbow.math.finite.bellman-signed-value-iteration-general-converges`](../src/rainbow/math/finite/bellman_signed_value_iteration_general_converges.clj) | General strict-rate convergence for signed Bellman value iteration. |
| [`rainbow.math.finite.bellman-stationary-policy-optimal`](../src/rainbow/math/finite/bellman_stationary_policy_optimal.clj) | A concrete optimal-policy theorem for exact finite NNRAT Bellman models. |
| [`rainbow.math.finite.bellman-value-iteration-converges`](../src/rainbow/math/finite/bellman_value_iteration_converges.clj) | Uniform additive convergence bounds for finite Bellman value iteration. |
| [`rainbow.math.finite.bellman-value-optimality`](../src/rainbow/math/finite/bellman_value_optimality.clj) | Normalized finite NNRAT expectation bounds and Bellman contractions. |
| [`rainbow.math.finite.bellman-value-optimality-theorem`](../src/rainbow/math/finite/bellman_value_optimality_theorem.clj) | Abstract, reduction-safe capstones for finite Bellman value iteration. |
| [`rainbow.math.finite.expectation`](../src/rainbow/math/finite/expectation.clj) | Executable finite natural mass and expectation numerators. |
| [`rainbow.math.finite.greedy-optimal`](../src/rainbow/math/finite/greedy_optimal.clj) | Greedy policy extraction from a finite nnrat Bellman fixed point. |
| [`rainbow.math.finite.index`](../src/rainbow/math/finite/index.clj) | Axiom-free bounded indices as a structural finite family. |
| [`rainbow.math.finite.index-hastings`](../src/rainbow/math/finite/index_hastings.clj) | The canonical Hastings kernel instantiated on structural finite indices. |
| [`rainbow.math.finite.index-hastings-coefficient`](../src/rainbow/math/finite/index_hastings_coefficient.clj) | Explicit proper Dobrushin factors for canonical Hastings on Index(n+1). |
| [`rainbow.math.finite.index-hastings-ergodic`](../src/rainbow/math/finite/index_hastings_ergodic.clj) | The finite ergodic theorem, instantiated for canonical Hastings kernels. |
| [`rainbow.math.finite.markov-aperiodicity`](../src/rainbow/math/finite/markov_aperiodicity.clj) | Aperiodicity from exact finite-state return horizons. |
| [`rainbow.math.finite.markov-cesaro`](../src/rainbow/math/finite/markov_cesaro.clj) | Finite Cesaro occupation sums and averages for exact NNRAT Markov dynamics. |
| [`rainbow.math.finite.markov-column-exact-contraction`](../src/rainbow/math/finite/markov_column_exact_contraction.clj) | Exact column-minimum coefficient and its positive-total properness. |
| [`rainbow.math.finite.markov-column-minorization`](../src/rainbow/math/finite/markov_column_minorization.clj) | Construct a shared lower mass by taking a finite minimum in each column. |
| [`rainbow.math.finite.markov-contraction-uniqueness`](../src/rainbow/math/finite/markov_contraction_uniqueness.clj) | Stationary-distribution uniqueness, conditional on one named inequality. |
| [`rainbow.math.finite.markov-coupling-coefficient`](../src/rainbow/math/finite/markov_coupling_coefficient.clj) | Charge off-diagonal residual coupling costs to the Dobrushin coefficient. |
| [`rainbow.math.finite.markov-coupling-distance`](../src/rainbow/math/finite/markov_coupling_distance.clj) | Off-diagonal kernel-row distance bound from a coupling's two marginals. |
| [`rainbow.math.finite.markov-dobrushin`](../src/rainbow/math/finite/markov_dobrushin.clj) | Maximum of a supplied NNRAT distance list, for a finite Dobrushin coefficient. |
| [`rainbow.math.finite.markov-dobrushin-contraction`](../src/rainbow/math/finite/markov_dobrushin_contraction.clj) | Inhabitant of the frozen finite Dobrushin contraction predicate. |
| [`rainbow.math.finite.markov-dobrushin-kernel`](../src/rainbow/math/finite/markov_dobrushin_kernel.clj) | Dobrushin coefficient constructed from every pair of enumerated kernel rows. |
| [`rainbow.math.finite.markov-dobrushin-statement`](../src/rainbow/math/finite/markov_dobrushin_statement.clj) | Formal proposition for the finite Dobrushin contraction estimate. |
| [`rainbow.math.finite.markov-ergodic-hypotheses`](../src/rainbow/math/finite/markov_ergodic_hypotheses.clj) | The exact finite-chain hypotheses needed by a future ergodic theorem. |
| [`rainbow.math.finite.markov-ergodic-uniqueness`](../src/rainbow/math/finite/markov_ergodic_uniqueness.clj) | Uniqueness of stationary distributions under a certified Dobrushin bound. |
| [`rainbow.math.finite.markov-expectation-invariance`](../src/rainbow/math/finite/markov_expectation_invariance.clj) | Exact observable invariance under stationary finite Markov dynamics. |
| [`rainbow.math.finite.markov-expectation-tower`](../src/rainbow/math/finite/markov_expectation_tower.clj) | The exact finite Markov expectation tower law over NNRAT. |
| [`rainbow.math.finite.markov-full-support`](../src/rainbow/math/finite/markov_full_support.clj) | An executable full-support decision, and what its verdict is worth. |
| [`rainbow.math.finite.markov-full-support-irreducible`](../src/rainbow/math/finite/markov_full_support_irreducible.clj) | Executable full support certifies irreducibility of finite Index kernels. |
| [`rainbow.math.finite.markov-geometric-convergence`](../src/rainbow/math/finite/markov_geometric_convergence.clj) | Iterates converge to the stationary distribution at geometric rate. |
| [`rainbow.math.finite.markov-geometric-decay`](../src/rainbow/math/finite/markov_geometric_decay.clj) | Geometric decay of total variation along kernel iterates. |
| [`rainbow.math.finite.markov-hastings-diagonal`](../src/rainbow/math/finite/markov_hastings_diagonal.clj) | The canonical diagonal rejection placement, from a Boolean equality decider. |
| [`rainbow.math.finite.markov-hastings-flow`](../src/rainbow/math/finite/markov_hastings_flow.clj) | General, division-free Hastings accepted-flow certificates. |
| [`rainbow.math.finite.markov-hastings-positive`](../src/rainbow/math/finite/markov_hastings_positive.clj) | Strict-positivity certificates for division-free Hastings transitions. |
| [`rainbow.math.finite.markov-iteration`](../src/rainbow/math/finite/markov_iteration.clj) | Certified finite-horizon iteration of an exact NNRAT Markov kernel. |
| [`rainbow.math.finite.markov-iteration-semigroup`](../src/rainbow/math/finite/markov_iteration_semigroup.clj) | Semigroup law for finite exact-rational Markov iteration. |
| [`rainbow.math.finite.markov-kernel-algebra`](../src/rainbow/math/finite/markov_kernel_algebra.clj) | Congruence, associativity, and observable action for exact finite kernels. |
| [`rainbow.math.finite.markov-kernel-composition`](../src/rainbow/math/finite/markov_kernel_composition.clj) | Composition laws for exact finite NNRAT Markov kernels. |
| [`rainbow.math.finite.markov-kernel-composition-positive`](../src/rainbow/math/finite/markov_kernel_composition_positive.clj) | Positive witnesses for finite exact-rational kernel composition. |
| [`rainbow.math.finite.markov-kernel-minimum`](../src/rainbow/math/finite/markov_kernel_minimum.clj) | A certified global minimum entry of a finite exact-rational kernel. |
| [`rainbow.math.finite.markov-metropolis-hastings`](../src/rainbow/math/finite/markov_metropolis_hastings.clj) | A fully checked finite Metropolis--Hastings independence sampler. |
| [`rainbow.math.finite.markov-minorization`](../src/rainbow/math/finite/markov_minorization.clj) | Finite shared lower-mass certificates for Dobrushin bounds. |
| [`rainbow.math.finite.markov-minorization-complement`](../src/rainbow/math/finite/markov_minorization_complement.clj) | Exact complementary-mass bounds, without a raw-denominator approximation. |
| [`rainbow.math.finite.markov-mixture-statement`](../src/rainbow/math/finite/markov_mixture_statement.clj) | Formal target for the finite residual-mixture inequality used by Dobrushin. |
| [`rainbow.math.finite.markov-overlap`](../src/rainbow/math/finite/markov_overlap.clj) | Shared-mass certificates for finite Dobrushin bounds. |
| [`rainbow.math.finite.markov-point-mass`](../src/rainbow/math/finite/markov_point_mass.clj) | Canonical point masses for finite exact-rational Markov kernels. |
| [`rainbow.math.finite.markov-positive-coefficient`](../src/rainbow/math/finite/markov_positive_coefficient.clj) | Explicit Dobrushin factors from a positive finite kernel minimum. |
| [`rainbow.math.finite.markov-positive-step`](../src/rainbow/math/finite/markov_positive_step.clj) | Positive support propagation through a finite exact-rational kernel. |
| [`rainbow.math.finite.markov-reachability`](../src/rainbow/math/finite/markov_reachability.clj) | Finite-step reachability and irreducibility for exact finite Markov kernels. |
| [`rainbow.math.finite.markov-reachability-witness`](../src/rainbow/math/finite/markov_reachability_witness.clj) | Existential finite-horizon witnesses for exact-rational Markov support. |
| [`rainbow.math.finite.markov-residual-coupling`](../src/rainbow/math/finite/markov_residual_coupling.clj) | Residual mass balance and constructive product-coupling marginals. |
| [`rainbow.math.finite.markov-residual-expansion`](../src/rainbow/math/finite/markov_residual_expansion.clj) | Canonical common mass cancels after a kernel step. |
| [`rainbow.math.finite.markov-residual-mixture-bound`](../src/rainbow/math/finite/markov_residual_mixture_bound.clj) | Markov-facing interface for the finite residual mixture inequality. |
| [`rainbow.math.finite.markov-return-time`](../src/rainbow/math/finite/markov_return_time.clj) | Fixed-horizon return evidence for exact finite Markov kernels. |
| [`rainbow.math.finite.markov-stationarity`](../src/rainbow/math/finite/markov_stationarity.clj) | Exact finite NNRAT Markov kernels, detailed balance, and stationarity. |
| [`rainbow.math.finite.markov-stationary-iterate`](../src/rainbow/math/finite/markov_stationary_iterate.clj) | A stationary distribution is fixed by every kernel iterate. |
| [`rainbow.math.finite.markov-total-variation`](../src/rainbow/math/finite/markov_total_variation.clj) | Total-variation distance between finite exact-rational distributions, and the separation half of the coming ergodic theorem. |
| [`rainbow.math.finite.markov-total-variation-bound`](../src/rainbow/math/finite/markov_total_variation_bound.clj) | Normalized finite total variation and its stochastic-row unit bound. |
| [`rainbow.math.finite.markov-total-variation-translation`](../src/rainbow/math/finite/markov_total_variation_translation.clj) | Common finite mass cancels from L1 and normalized total variation. |
| [`rainbow.math.finite.matrix`](../src/rainbow/math/finite/matrix.clj) | Finite signed-rational matrices and their native action on vectors. |
| [`rainbow.math.finite.metric`](../src/rainbow/math/finite/metric.clj) | Constructive maximum folds and finite sup-distance over exact finite data. |
| [`rainbow.math.finite.metric-separation`](../src/rainbow/math/finite/metric_separation.clj) | Constructive zero and positivity separation for finite natural sup-distance. |
| [`rainbow.math.finite.nnrat-sup-distance`](../src/rainbow/math/finite/nnrat_sup_distance.clj) | A native finite supremum metric for NNRAT-valued functions. |
| [`rainbow.math.finite.nnrat-sup-radius`](../src/rainbow/math/finite/nnrat_sup_radius.clj) | A Bellman-compatible NNRAT supremum radius over exact finite carriers. |
| [`rainbow.math.finite.policy-evaluation`](../src/rainbow/math/finite/policy_evaluation.clj) | AHoF D20: bounded finite-policy evaluation over exact rational data. |
| [`rainbow.math.finite.policy-improvement`](../src/rainbow/math/finite/policy_improvement.clj) | Policy-iteration monotonic improvement (Q-score level): the greedy-improved policy's action-score dominates the current policy's at every state. |
| [`rainbow.math.finite.policy-iteration`](../src/rainbow/math/finite/policy_iteration.clj) | Finite exact-rational policy improvement and one composed iteration step. |
| [`rainbow.math.finite.policy-iteration-optimal`](../src/rainbow/math/finite/policy_iteration_optimal.clj) | Stationary finite-policy improvement implies the optimal Bellman equation. |
| [`rainbow.math.finite.policy-value-dominance`](../src/rainbow/math/finite/policy_value_dominance.clj) | Abstract, reduction-safe policy-improvement value dominance for finite nnrat MDPs. |
| [`rainbow.math.finite.powerset`](../src/rainbow/math/finite/powerset.clj) | Finite powersets, infinite suprema, and subtype projection injectivity. |
| [`rainbow.math.finite.rational-argmax`](../src/rainbow/math/finite/rational_argmax.clj) | Executable finite argmax with exact rational dominance certificates. |
| [`rainbow.math.finite.rational-argmin`](../src/rainbow/math/finite/rational_argmin.clj) | Executable finite argmin with exact rational minimality certificates. |
| [`rainbow.math.finite.rational-expectation`](../src/rainbow/math/finite/rational_expectation.clj) | Finite nonnegative-rational folds and expectations with congruence proofs. |
| [`rainbow.math.finite.set`](../src/rainbow/math/finite/set.clj) | Constructive finite-set theorems over native List-cover proof data. |
| [`rainbow.math.finite.set-boundary`](../src/rainbow/math/finite/set_boundary.clj) | Classical boundary facts for native finite and infinite sets. |
| [`rainbow.math.finite.set-classical`](../src/rainbow/math/finite/set_classical.clj) | Classical finite-set transport, kept separate from the axiom-free layer. |
| [`rainbow.math.finite.set-fiber`](../src/rainbow/math/finite/set_fiber.clj) | Constructive finite fibers inside finite source sets. |
| [`rainbow.math.finite.set-fiber-decomposition`](../src/rainbow/math/finite/set_fiber_decomposition.clj) | A finite source is the union of its fibers over its finite image. |
| [`rainbow.math.finite.set-image2-infinite`](../src/rainbow/math/finite/set_image2_infinite.clj) | Infinitude transport through binary images and Cartesian products. |
| [`rainbow.math.finite.set-indexed-union`](../src/rainbow/math/finite/set_indexed_union.clj) | Constructive finite unions over finite index sets. |
| [`rainbow.math.finite.set-inverse-transport`](../src/rainbow/math/finite/set_inverse_transport.clj) | Constructive finiteness and infinitude transport across explicit set inverses. |
| [`rainbow.math.finite.set-lattice`](../src/rainbow/math/finite/set_lattice.clj) | Finite-set closure facts for complements, intersections, and suprema. |
| [`rainbow.math.finite.set-union`](../src/rainbow/math/finite/set_union.clj) | Reusable finite/infinite union facts as native proof data. |
| [`rainbow.math.finite.signed-approximate-fixed-point-sup`](../src/rainbow/math/finite/signed_approximate_fixed_point_sup.clj) | Finite-sup certificates from pointwise signed approximate fixed points. |
| [`rainbow.math.finite.signed-argmax`](../src/rainbow/math/finite/signed_argmax.clj) | Executable finite argmax over exact signed-rational scores. |
| [`rainbow.math.finite.signed-argmax-nonexpansive`](../src/rainbow/math/finite/signed_argmax_nonexpansive.clj) | Additive nonexpansiveness of runtime-length finite signed-rational argmax. |
| [`rainbow.math.finite.signed-expectation`](../src/rainbow/math/finite/signed_expectation.clj) | Normalized finite expectation for exact signed-rational outcomes. |
| [`rainbow.math.finite.signed-sup-distance`](../src/rainbow/math/finite/signed_sup_distance.clj) | A native finite supremum metric for signed-valued functions. |
| [`rainbow.math.finite.signed-sup-separation`](../src/rainbow/math/finite/signed_sup_separation.clj) | Exact separation for finite signed-valued function sup distance. |
| [`rainbow.math.finite.subtype`](../src/rainbow/math/finite/subtype.clj) | Finite propositions and finite-subtype bridges as checked proof data. |
| [`rainbow.math.finite.type`](../src/rainbow/math/finite/type.clj) | Native finite and infinite carrier propositions as finite List covers. |
| [`rainbow.math.finite.value-iteration`](../src/rainbow/math/finite/value_iteration.clj) | Finite Bellman optimality and bounded value iteration over exact rationals. |
| [`rainbow.math.finite.vector`](../src/rainbow/math/finite/vector.clj) | Finite vectors over signed rationals: lists of signed-rational components with elementwise addition, negation, subtraction, and scalar scaling. |

## Lemmas behind operations-research checks (`src/rainbow/math/lemmas/`, 104)

| namespace | |
|---|---|
| [`rainbow.math.lemmas.abc-class`](../src/rainbow/math/lemmas/abc_class.clj) | General lemmas: abc class. |
| [`rainbow.math.lemmas.acf-bound`](../src/rainbow/math/lemmas/acf_bound.clj) | General lemmas: acf bound. |
| [`rainbow.math.lemmas.aggplan-balance`](../src/rainbow/math/lemmas/aggplan_balance.clj) | General lemmas: aggplan balance. |
| [`rainbow.math.lemmas.anova-readings`](../src/rainbow/math/lemmas/anova_readings.clj) | General lemmas: anova readings. |
| [`rainbow.math.lemmas.assign-dual`](../src/rainbow/math/lemmas/assign_dual.clj) | General lemmas: assign dual. |
| [`rainbow.math.lemmas.auc-readings`](../src/rainbow/math/lemmas/auc_readings.clj) | General lemmas: auc readings. |
| [`rainbow.math.lemmas.auction-assignment`](../src/rainbow/math/lemmas/auction_assignment.clj) | General lemmas: auction assignment. |
| [`rainbow.math.lemmas.basestock-readings`](../src/rainbow/math/lemmas/basestock_readings.clj) | General lemmas: basestock readings. |
| [`rainbow.math.lemmas.battery-readings`](../src/rainbow/math/lemmas/battery_readings.clj) | General lemmas: battery readings. |
| [`rainbow.math.lemmas.bb-leaf-bound`](../src/rainbow/math/lemmas/bb_leaf_bound.clj) | General lemmas: bb leaf bound. |
| [`rainbow.math.lemmas.benders-cut`](../src/rainbow/math/lemmas/benders_cut.clj) | General lemmas: benders cut. |
| [`rainbow.math.lemmas.bin-packing-bound`](../src/rainbow/math/lemmas/bin_packing_bound.clj) | General lemmas: bin packing bound. |
| [`rainbow.math.lemmas.borda`](../src/rainbow/math/lemmas/borda.clj) | General lemmas: borda. |
| [`rainbow.math.lemmas.bottleneck-assignment`](../src/rainbow/math/lemmas/bottleneck_assignment.clj) | General lemmas: bottleneck assignment. |
| [`rainbow.math.lemmas.capital-ratio`](../src/rainbow/math/lemmas/capital_ratio.clj) | General lemmas: capital ratio. |
| [`rainbow.math.lemmas.capm-normal`](../src/rainbow/math/lemmas/capm_normal.clj) | General lemmas: capm normal. |
| [`rainbow.math.lemmas.cashbudget-balance`](../src/rainbow/math/lemmas/cashbudget_balance.clj) | General lemmas: cashbudget balance. |
| [`rainbow.math.lemmas.cea-rule`](../src/rainbow/math/lemmas/cea_rule.clj) | General lemmas: cea rule. |
| [`rainbow.math.lemmas.census-readings`](../src/rainbow/math/lemmas/census_readings.clj) | General lemmas: census readings. |
| [`rainbow.math.lemmas.chisq-readings`](../src/rainbow/math/lemmas/chisq_readings.clj) | General lemmas: chisq readings. |
| [`rainbow.math.lemmas.claimpay-readings`](../src/rainbow/math/lemmas/claimpay_readings.clj) | General lemmas: claimpay readings. |
| [`rainbow.math.lemmas.clv-geometric`](../src/rainbow/math/lemmas/clv_geometric.clj) | General lemmas: clv geometric. |
| [`rainbow.math.lemmas.combined-ratio`](../src/rainbow/math/lemmas/combined_ratio.clj) | General lemmas: combined ratio. |
| [`rainbow.math.lemmas.cournot-readings`](../src/rainbow/math/lemmas/cournot_readings.clj) | General lemmas: cournot readings. |
| [`rainbow.math.lemmas.cover-cut`](../src/rainbow/math/lemmas/cover_cut.clj) | General lemmas: cover cut. |
| [`rainbow.math.lemmas.cpm-makespan`](../src/rainbow/math/lemmas/cpm_makespan.clj) | General lemmas: cpm makespan. |
| [`rainbow.math.lemmas.crash-readings`](../src/rainbow/math/lemmas/crash_readings.clj) | General lemmas: crash readings. |
| [`rainbow.math.lemmas.credibility-readings`](../src/rainbow/math/lemmas/credibility_readings.clj) | General lemmas: credibility readings. |
| [`rainbow.math.lemmas.dc-power-flow`](../src/rainbow/math/lemmas/dc_power_flow.clj) | General lemmas: dc power flow. |
| [`rainbow.math.lemmas.dea-efficiency`](../src/rainbow/math/lemmas/dea_efficiency.clj) | General lemmas: dea efficiency. |
| [`rainbow.math.lemmas.durbin-bounds`](../src/rainbow/math/lemmas/durbin_bounds.clj) | General lemmas: durbin bounds. |
| [`rainbow.math.lemmas.economic-dispatch`](../src/rainbow/math/lemmas/economic_dispatch.clj) | General lemmas: economic dispatch. |
| [`rainbow.math.lemmas.edf-readings`](../src/rainbow/math/lemmas/edf_readings.clj) | General lemmas: edf readings. |
| [`rainbow.math.lemmas.fcast-readings`](../src/rainbow/math/lemmas/fcast_readings.clj) | General lemmas: fcast readings. |
| [`rainbow.math.lemmas.fgt-order`](../src/rainbow/math/lemmas/fgt_order.clj) | General lemmas: fgt order. |
| [`rainbow.math.lemmas.frankw-corner`](../src/rainbow/math/lemmas/frankw_corner.clj) | General lemmas: frankw corner. |
| [`rainbow.math.lemmas.fulfil-readings`](../src/rainbow/math/lemmas/fulfil_readings.clj) | General lemmas: fulfil readings. |
| [`rainbow.math.lemmas.game-value`](../src/rainbow/math/lemmas/game_value.clj) | General lemmas: game value. |
| [`rainbow.math.lemmas.gilmore-pricing`](../src/rainbow/math/lemmas/gilmore_pricing.clj) | General lemmas: gilmore pricing. |
| [`rainbow.math.lemmas.headway-wait`](../src/rainbow/math/lemmas/headway_wait.clj) | General lemmas: headway wait. |
| [`rainbow.math.lemmas.hhi-bounds`](../src/rainbow/math/lemmas/hhi_bounds.clj) | General lemmas: hhi bounds. |
| [`rainbow.math.lemmas.hungarian-bound`](../src/rainbow/math/lemmas/hungarian_bound.clj) | General lemmas: hungarian bound. |
| [`rainbow.math.lemmas.incometax-readings`](../src/rainbow/math/lemmas/incometax_readings.clj) | General lemmas: incometax readings. |
| [`rainbow.math.lemmas.indep-set-dual`](../src/rainbow/math/lemmas/indep_set_dual.clj) | General lemmas: indep set dual. |
| [`rainbow.math.lemmas.infnorm-abs`](../src/rainbow/math/lemmas/infnorm_abs.clj) | General lemmas: infnorm abs. |
| [`rainbow.math.lemmas.ista-shrink`](../src/rainbow/math/lemmas/ista_shrink.clj) | General lemmas: ista shrink. |
| [`rainbow.math.lemmas.kmeans-nearest`](../src/rainbow/math/lemmas/kmeans_nearest.clj) | General lemmas: kmeans nearest. |
| [`rainbow.math.lemmas.knn-reading`](../src/rainbow/math/lemmas/knn_reading.clj) | General lemmas: knn reading. |
| [`rainbow.math.lemmas.kstwo-range`](../src/rainbow/math/lemmas/kstwo_range.clj) | General lemmas: kstwo range. |
| [`rainbow.math.lemmas.lcr-floor`](../src/rainbow/math/lemmas/lcr_floor.clj) | General lemmas: lcr floor. |
| [`rainbow.math.lemmas.lp-duality`](../src/rainbow/math/lemmas/lp_duality.clj) | General lemmas: lp duality. |
| [`rainbow.math.lemmas.lp-farkas`](../src/rainbow/math/lemmas/lp_farkas.clj) | General lemmas: lp farkas. |
| [`rainbow.math.lemmas.lp-ray`](../src/rainbow/math/lemmas/lp_ray.clj) | General lemmas: lp ray. |
| [`rainbow.math.lemmas.lsq-optimal`](../src/rainbow/math/lemmas/lsq_optimal.clj) | General lemmas: lsq optimal. |
| [`rainbow.math.lemmas.masshaul-readings`](../src/rainbow/math/lemmas/masshaul_readings.clj) | General lemmas: masshaul readings. |
| [`rainbow.math.lemmas.matching-cover-duality`](../src/rainbow/math/lemmas/matching_cover_duality.clj) | General lemmas: matching cover duality. |
| [`rainbow.math.lemmas.max-closure`](../src/rainbow/math/lemmas/max_closure.clj) | General lemmas: max closure. |
| [`rainbow.math.lemmas.mccormick-sandwich`](../src/rainbow/math/lemmas/mccormick_sandwich.clj) | General lemmas: mccormick sandwich. |
| [`rainbow.math.lemmas.mcf-optimal`](../src/rainbow/math/lemmas/mcf_optimal.clj) | General lemmas: mcf optimal. |
| [`rainbow.math.lemmas.mctrans-step`](../src/rainbow/math/lemmas/mctrans_step.clj) | General lemmas: mctrans step. |
| [`rainbow.math.lemmas.minimax-regret`](../src/rainbow/math/lemmas/minimax_regret.clj) | General lemmas: minimax regret. |
| [`rainbow.math.lemmas.mmck-unique`](../src/rainbow/math/lemmas/mmck_unique.clj) | General lemmas: mmck unique. |
| [`rainbow.math.lemmas.mnl-assortment`](../src/rainbow/math/lemmas/mnl_assortment.clj) | General lemmas: mnl assortment. |
| [`rainbow.math.lemmas.ncd-readings`](../src/rainbow/math/lemmas/ncd_readings.clj) | General lemmas: ncd readings. |
| [`rainbow.math.lemmas.ncyc-infeasible`](../src/rainbow/math/lemmas/ncyc_infeasible.clj) | General lemmas: ncyc infeasible. |
| [`rainbow.math.lemmas.nmb-decision`](../src/rainbow/math/lemmas/nmb_decision.clj) | General lemmas: nmb decision. |
| [`rainbow.math.lemmas.nsfr-reading`](../src/rainbow/math/lemmas/nsfr_reading.clj) | General lemmas: nsfr reading. |
| [`rainbow.math.lemmas.nvcost-readings`](../src/rainbow/math/lemmas/nvcost_readings.clj) | General lemmas: nvcost readings. |
| [`rainbow.math.lemmas.odd-cycle-cut`](../src/rainbow/math/lemmas/odd_cycle_cut.clj) | General lemmas: odd cycle cut. |
| [`rainbow.math.lemmas.oee-factors`](../src/rainbow/math/lemmas/oee_factors.clj) | General lemmas: oee factors. |
| [`rainbow.math.lemmas.one-center`](../src/rainbow/math/lemmas/one_center.clj) | General lemmas: one center. |
| [`rainbow.math.lemmas.payasbid-readings`](../src/rainbow/math/lemmas/payasbid_readings.clj) | General lemmas: payasbid readings. |
| [`rainbow.math.lemmas.pcmax-lower-bound`](../src/rainbow/math/lemmas/pcmax_lower_bound.clj) | General lemmas: pcmax lower bound. |
| [`rainbow.math.lemmas.pfs-readings`](../src/rainbow/math/lemmas/pfs_readings.clj) | General lemmas: pfs readings. |
| [`rainbow.math.lemmas.pindex-readings`](../src/rainbow/math/lemmas/pindex_readings.clj) | General lemmas: pindex readings. |
| [`rainbow.math.lemmas.prf-readings`](../src/rainbow/math/lemmas/prf_readings.clj) | General lemmas: prf readings. |
| [`rainbow.math.lemmas.projgrad-clamp`](../src/rainbow/math/lemmas/projgrad_clamp.clj) | General lemmas: projgrad clamp. |
| [`rainbow.math.lemmas.qp-kkt`](../src/rainbow/math/lemmas/qp_kkt.clj) | General lemmas: qp kkt. |
| [`rainbow.math.lemmas.rccp-readings`](../src/rainbow/math/lemmas/rccp_readings.clj) | General lemmas: rccp readings. |
| [`rainbow.math.lemmas.reservoir-readings`](../src/rainbow/math/lemmas/reservoir_readings.clj) | General lemmas: reservoir readings. |
| [`rainbow.math.lemmas.rippl-readings`](../src/rainbow/math/lemmas/rippl_readings.clj) | General lemmas: rippl readings. |
| [`rainbow.math.lemmas.salesq-readings`](../src/rainbow/math/lemmas/salesq_readings.clj) | General lemmas: salesq readings. |
| [`rainbow.math.lemmas.sigtime-readings`](../src/rainbow/math/lemmas/sigtime_readings.clj) | General lemmas: sigtime readings. |
| [`rainbow.math.lemmas.sir-readings`](../src/rainbow/math/lemmas/sir_readings.clj) | General lemmas: sir readings. |
| [`rainbow.math.lemmas.slo-budget`](../src/rainbow/math/lemmas/slo_budget.clj) | General lemmas: slo budget. |
| [`rainbow.math.lemmas.sproj-projection`](../src/rainbow/math/lemmas/sproj_projection.clj) | General lemmas: sproj projection. |
| [`rainbow.math.lemmas.sspol-readings`](../src/rainbow/math/lemmas/sspol_readings.clj) | General lemmas: sspol readings. |
| [`rainbow.math.lemmas.state-price`](../src/rainbow/math/lemmas/state_price.clj) | General lemmas: state price. |
| [`rainbow.math.lemmas.stochastic-dominance`](../src/rainbow/math/lemmas/stochastic_dominance.clj) | General lemmas: stochastic dominance. |
| [`rainbow.math.lemmas.stoploss-bounds`](../src/rainbow/math/lemmas/stoploss_bounds.clj) | General lemmas: stoploss bounds. |
| [`rainbow.math.lemmas.subgrad-duality`](../src/rainbow/math/lemmas/subgrad_duality.clj) | General lemmas: subgrad duality. |
| [`rainbow.math.lemmas.transport-dual`](../src/rainbow/math/lemmas/transport_dual.clj) | General lemmas: transport dual. |
| [`rainbow.math.lemmas.trigg-bound`](../src/rainbow/math/lemmas/trigg_bound.clj) | General lemmas: trigg bound. |
| [`rainbow.math.lemmas.twoline-readings`](../src/rainbow/math/lemmas/twoline_readings.clj) | General lemmas: twoline readings. |
| [`rainbow.math.lemmas.ufl-gap`](../src/rainbow/math/lemmas/ufl_gap.clj) | General lemmas: ufl gap. |
| [`rainbow.math.lemmas.unifpx-readings`](../src/rainbow/math/lemmas/unifpx_readings.clj) | General lemmas: unifpx readings. |
| [`rainbow.math.lemmas.vertex-cover-approx`](../src/rainbow/math/lemmas/vertex_cover_approx.clj) | General lemmas: vertex cover approx. |
| [`rainbow.math.lemmas.vickrey-dsic`](../src/rainbow/math/lemmas/vickrey_dsic.clj) | General lemmas: vickrey dsic. |
| [`rainbow.math.lemmas.voter-readings`](../src/rainbow/math/lemmas/voter_readings.clj) | General lemmas: voter readings. |
| [`rainbow.math.lemmas.wab-mean`](../src/rainbow/math/lemmas/wab_mean.clj) | General lemmas: wab mean. |
| [`rainbow.math.lemmas.wage-readings`](../src/rainbow/math/lemmas/wage_readings.clj) | General lemmas: wage readings. |
| [`rainbow.math.lemmas.weighted-cover-rounding`](../src/rainbow/math/lemmas/weighted_cover_rounding.clj) | General lemmas: weighted cover rounding. |
| [`rainbow.math.lemmas.weighted-median`](../src/rainbow/math/lemmas/weighted_median.clj) | General lemmas: weighted median. |
| [`rainbow.math.lemmas.xol-readings`](../src/rainbow/math/lemmas/xol_readings.clj) | General lemmas: xol readings. |

## Matrices (`src/rainbow/math/linear/matrix/`, 100)

| namespace | |
|---|---|
| [`rainbow.math.linear.matrix.action-associative`](../src/rainbow/math/linear/matrix/action_associative.clj) | Finite matrix action is adjoint to native transpose. |
| [`rainbow.math.linear.matrix.action-prepend`](../src/rainbow/math/linear/matrix/action_prepend.clj) | Action laws for inserting a leading column into a native finite matrix. |
| [`rainbow.math.linear.matrix.action-scale`](../src/rainbow/math/linear/matrix/action_scale.clj) | Arbitrary signed-scalar vector scaling for native matrix algebra. |
| [`rainbow.math.linear.matrix.action-sup-bound`](../src/rainbow/math/linear/matrix/action_sup_bound.clj) | Lift rowwise dot-distance bounds to a matrix-action sup bound. |
| [`rainbow.math.linear.matrix.add`](../src/rainbow/math/linear/matrix/add.clj) | Length-sensitive shape, addition, and left distributivity for matrices. |
| [`rainbow.math.linear.matrix.add-algebra`](../src/rainbow/math/linear/matrix/add_algebra.clj) | Commutative, associative, quotient-safe native matrix addition. |
| [`rainbow.math.linear.matrix.add-order`](../src/rainbow/math/linear/matrix/add_order.clj) | Pointwise order laws for native matrix addition and subtraction. |
| [`rainbow.math.linear.matrix.add-right`](../src/rainbow/math/linear/matrix/add_right.clj) | Transpose additivity and right distributivity for native matrices. |
| [`rainbow.math.linear.matrix.add-shape`](../src/rainbow/math/linear/matrix/add_shape.clj) | Equivalence laws for matrix shape and shape preservation by addition. |
| [`rainbow.math.linear.matrix.additive-group`](../src/rainbow/math/linear/matrix/additive_group.clj) | Shaped zero, negation, subtraction, and inverse laws for matrices. |
| [`rainbow.math.linear.matrix.affine-approximate-fixed-point`](../src/rainbow/math/linear/matrix/affine_approximate_fixed_point.clj) | Constructive approximate fixed points from affine residual convergence. |
| [`rainbow.math.linear.matrix.affine-approximate-offset-stability`](../src/rainbow/math/linear/matrix/affine_approximate_offset_stability.clj) | Robust stability for approximate solutions under offset perturbation. |
| [`rainbow.math.linear.matrix.affine-approximate-stability`](../src/rainbow/math/linear/matrix/affine_approximate_stability.clj) | A posteriori stability of approximate affine fixed points. |
| [`rainbow.math.linear.matrix.affine-bracket-collapse`](../src/rainbow/math/linear/matrix/affine_bracket_collapse.clj) | Exact convergence certificates from collapsed affine brackets. |
| [`rainbow.math.linear.matrix.affine-bracket-uniqueness`](../src/rainbow/math/linear/matrix/affine_bracket_uniqueness.clj) | Affine fixed-point uniqueness inside a collapsed monotone bracket. |
| [`rainbow.math.linear.matrix.affine-equivalence`](../src/rainbow/math/linear/matrix/affine_equivalence.clj) | Congruence and fixed-point invariance for signed affine value iteration. |
| [`rainbow.math.linear.matrix.affine-fixed-point-order`](../src/rainbow/math/linear/matrix/affine_fixed_point_order.clj) | Order bounds for finite signed affine iteration around a fixed point. |
| [`rainbow.math.linear.matrix.affine-general-rate-certificate`](../src/rainbow/math/linear/matrix/affine_general_rate_certificate.clj) | Sharp affine residual certificates for every canonical rational rate below one. |
| [`rainbow.math.linear.matrix.affine-general-rate-iterate-certificate`](../src/rainbow/math/linear/matrix/affine_general_rate_iterate_certificate.clj) | Sharp finite-horizon iterate error at every canonical rational rate. |
| [`rainbow.math.linear.matrix.affine-general-rate-sensitivity`](../src/rainbow/math/linear/matrix/affine_general_rate_sensitivity.clj) | Sharp robustness certificates for arbitrary-rate affine problem drift. |
| [`rainbow.math.linear.matrix.affine-general-rate-tail-certificate`](../src/rainbow/math/linear/matrix/affine_general_rate_tail_certificate.clj) | Sharp fixed-point-free tail certificates at arbitrary rational rates. |
| [`rainbow.math.linear.matrix.affine-general-rate-uniqueness`](../src/rainbow/math/linear/matrix/affine_general_rate_uniqueness.clj) | Fixed-point uniqueness for every canonical rational row-sum contraction. |
| [`rainbow.math.linear.matrix.affine-half-iterate-contraction`](../src/rainbow/math/linear/matrix/affine_half_iterate_contraction.clj) | Shape preservation and one-step contraction for half-row affine iteration. |
| [`rainbow.math.linear.matrix.affine-half-iterate-converges`](../src/rainbow/math/linear/matrix/affine_half_iterate_converges.clj) | Rate-null convergence for half-row signed affine iteration. |
| [`rainbow.math.linear.matrix.affine-half-iterate-rate`](../src/rainbow/math/linear/matrix/affine_half_iterate_rate.clj) | Finite-horizon geometric rate for half-row signed affine iteration. |
| [`rainbow.math.linear.matrix.affine-horizon-order`](../src/rainbow/math/linear/matrix/affine_horizon_order.clj) | Composition and arbitrary-horizon order for finite affine iteration. |
| [`rainbow.math.linear.matrix.affine-invariant-interval`](../src/rainbow/math/linear/matrix/affine_invariant_interval.clj) | Invariant intervals for finite signed affine value iteration. |
| [`rainbow.math.linear.matrix.affine-inverse-gap-certificate`](../src/rainbow/math/linear/matrix/affine_inverse_gap_certificate.clj) | Sharp residual certificates for arbitrary strict contraction rates. |
| [`rainbow.math.linear.matrix.affine-inverse-gap-stability`](../src/rainbow/math/linear/matrix/affine_inverse_gap_stability.clj) | Sharp stability of two approximate affine solutions at arbitrary rates. |
| [`rainbow.math.linear.matrix.affine-iterate`](../src/rainbow/math/linear/matrix/affine_iterate.clj) | Finite signed value iteration for affine matrix maps. |
| [`rainbow.math.linear.matrix.affine-nnrat-exact-rate`](../src/rainbow/math/linear/matrix/affine_nnrat_exact_rate.clj) | Exact NNRAT-rate contraction and residual certificates. |
| [`rainbow.math.linear.matrix.affine-nnrat-exact-rate-null`](../src/rainbow/math/linear/matrix/affine_nnrat_exact_rate_null.clj) | Null-sequence bridges for exact NNRAT contraction envelopes. |
| [`rainbow.math.linear.matrix.affine-offset-sensitivity`](../src/rainbow/math/linear/matrix/affine_offset_sensitivity.clj) | Sensitivity of contractive affine fixed points to offset perturbations. |
| [`rainbow.math.linear.matrix.affine-operator-sensitivity`](../src/rainbow/math/linear/matrix/affine_operator_sensitivity.clj) | Approximate-solution stability across certified affine-map perturbations. |
| [`rainbow.math.linear.matrix.affine-order`](../src/rainbow/math/linear/matrix/affine_order.clj) | Order and interval laws for signed affine finite-matrix action. |
| [`rainbow.math.linear.matrix.affine-problem-sensitivity`](../src/rainbow/math/linear/matrix/affine_problem_sensitivity.clj) | End-to-end robustness for approximate affine optimization problems. |
| [`rainbow.math.linear.matrix.affine-residual`](../src/rainbow/math/linear/matrix/affine_residual.clj) | Shape-safe residual characterization of affine fixed points. |
| [`rainbow.math.linear.matrix.affine-residual-bracket`](../src/rainbow/math/linear/matrix/affine_residual_bracket.clj) | Nested finite-horizon affine brackets from linear residual certificates. |
| [`rainbow.math.linear.matrix.affine-residual-certificate`](../src/rainbow/math/linear/matrix/affine_residual_certificate.clj) | A posteriori error certificates for contractive signed affine systems. |
| [`rainbow.math.linear.matrix.affine-residual-decay`](../src/rainbow/math/linear/matrix/affine_residual_decay.clj) | Geometric decay and finite-horizon error bounds from computable residuals. |
| [`rainbow.math.linear.matrix.affine-residual-iteration`](../src/rainbow/math/linear/matrix/affine_residual_iteration.clj) | Finite value-iteration guarantees from linear residual inequalities. |
| [`rainbow.math.linear.matrix.affine-residual-order`](../src/rainbow/math/linear/matrix/affine_residual_order.clj) | Residual order certificates for affine subsolutions and supersolutions. |
| [`rainbow.math.linear.matrix.affine-residual-stopping`](../src/rainbow/math/linear/matrix/affine_residual_stopping.clj) | Exact residual stopping certificates for finite affine value iteration. |
| [`rainbow.math.linear.matrix.affine-residual-uniqueness`](../src/rainbow/math/linear/matrix/affine_residual_uniqueness.clj) | Uniqueness of enclosed affine residual solutions after bracket collapse. |
| [`rainbow.math.linear.matrix.affine-sign`](../src/rainbow/math/linear/matrix/affine_sign.clj) | Cone preservation for vector addition and signed affine matrix action. |
| [`rainbow.math.linear.matrix.affine-stabilization`](../src/rainbow/math/linear/matrix/affine_stabilization.clj) | Exact finite stabilization of signed affine value iteration. |
| [`rainbow.math.linear.matrix.affine-strong-row-contraction`](../src/rainbow/math/linear/matrix/affine_strong_row_contraction.clj) | User-facing contraction results for any NNRAT row bound gamma <= 1/2. |
| [`rainbow.math.linear.matrix.affine-sup-distance`](../src/rainbow/math/linear/matrix/affine_sup_distance.clj) | Sup-distance cancellation and bound transfer for signed affine action. |
| [`rainbow.math.linear.matrix.affine-tail-diameter`](../src/rainbow/math/linear/matrix/affine_tail_diameter.clj) | Constructive tail diameter for contractive affine iteration. |
| [`rainbow.math.linear.matrix.affine-trajectory-order`](../src/rainbow/math/linear/matrix/affine_trajectory_order.clj) | Successive-order laws for finite signed affine value iteration. |
| [`rainbow.math.linear.matrix.antitone`](../src/rainbow/math/linear/matrix/antitone.clj) | Antitonicity of native dot products, matrix action, and multiplication. |
| [`rainbow.math.linear.matrix.associativity-counterexample`](../src/rainbow/math/linear/matrix/associativity_counterexample.clj) | A checked counterexample to unrestricted native matrix associativity. |
| [`rainbow.math.linear.matrix.composable`](../src/rainbow/math/linear/matrix/composable.clj) | Dimension certificates for native finite matrix composition. |
| [`rainbow.math.linear.matrix.composable-multiply`](../src/rainbow/math/linear/matrix/composable_multiply.clj) | Closure of matrix composability under native multiplication bracketings. |
| [`rainbow.math.linear.matrix.composable-transpose`](../src/rainbow/math/linear/matrix/composable_transpose.clj) | Composable native matrix pairs reverse under transpose. |
| [`rainbow.math.linear.matrix.equivalence`](../src/rainbow/math/linear/matrix/equivalence.clj) | Length-sensitive, row-wise equivalence for native finite matrices. |
| [`rainbow.math.linear.matrix.equivalence-shape`](../src/rainbow/math/linear/matrix/equivalence_shape.clj) | Shape transport for length-sensitive native matrix equivalence. |
| [`rainbow.math.linear.matrix.gram-kernel`](../src/rainbow/math/linear/matrix/gram_kernel.clj) | The zero kernel of the native Gram quadratic form. |
| [`rainbow.math.linear.matrix.gram-positive`](../src/rainbow/math/linear/matrix/gram_positive.clj) | Positive-semidefinite Gram action for native signed matrices. |
| [`rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness`](../src/rainbow/math/linear/matrix/half_row_sum_fixed_point_uniqueness.clj) | Concrete half-contractive uniqueness for signed affine row-sum systems. |
| [`rainbow.math.linear.matrix.interval-order`](../src/rainbow/math/linear/matrix/interval_order.clj) | Interval propagation for signed vectors and native finite matrices. |
| [`rainbow.math.linear.matrix.least-squares-equality`](../src/rainbow/math/linear/matrix/least_squares_equality.clj) | Equality and nullspace directions in exact finite least squares. |
| [`rainbow.math.linear.matrix.least-squares-normal`](../src/rainbow/math/linear/matrix/least_squares_normal.clj) | Normal-equation sufficiency for exact finite least squares. |
| [`rainbow.math.linear.matrix.linear`](../src/rainbow/math/linear/matrix/linear.clj) | Shape and scalar-linearity laws for native matrix-vector multiplication. |
| [`rainbow.math.linear.matrix.mixed-sign-action`](../src/rainbow/math/linear/matrix/mixed_sign_action.clj) | Mixed-sign laws for signed dot products and native matrix action. |
| [`rainbow.math.linear.matrix.mixed-sign-multiply`](../src/rainbow/math/linear/matrix/mixed_sign_multiply.clj) | Mixed-sign laws for native finite matrix multiplication. |
| [`rainbow.math.linear.matrix.multiply`](../src/rainbow/math/linear/matrix/multiply.clj) | Native matrix multiplication for row-major finite signed matrices. |
| [`rainbow.math.linear.matrix.multiply-associative`](../src/rainbow/math/linear/matrix/multiply_associative.clj) | Associativity of composable native finite matrix multiplication. |
| [`rainbow.math.linear.matrix.multiply-shape`](../src/rainbow/math/linear/matrix/multiply_shape.clj) | Unconditional output-shape laws for native matrix multiplication. |
| [`rainbow.math.linear.matrix.negate-linear`](../src/rainbow/math/linear/matrix/negate_linear.clj) | Negation commutes with native matrix action, transpose, and multiplication. |
| [`rainbow.math.linear.matrix.pointwise-order-laws`](../src/rainbow/math/linear/matrix/pointwise_order_laws.clj) | Partial-order and quotient-transport laws for native finite matrices. |
| [`rainbow.math.linear.matrix.positive-action`](../src/rainbow/math/linear/matrix/positive_action.clj) | Positive dot products and monotone native matrix-vector action. |
| [`rainbow.math.linear.matrix.positive-multiply`](../src/rainbow/math/linear/matrix/positive_multiply.clj) | Nonnegativity and monotonicity of native finite matrix multiplication. |
| [`rainbow.math.linear.matrix.prepend-add`](../src/rainbow/math/linear/matrix/prepend_add.clj) | Shape-safe additivity of total column insertion. |
| [`rainbow.math.linear.matrix.row-gram`](../src/rainbow/math/linear/matrix/row_gram.clj) | Symmetry and positive semidefiniteness of the native row Gram product. |
| [`rainbow.math.linear.matrix.row-gram-kernel`](../src/rainbow/math/linear/matrix/row_gram_kernel.clj) | Zero-kernel characterization for the native row Gram product AA^T. |
| [`rainbow.math.linear.matrix.row-length-decider`](../src/rainbow/math/linear/matrix/row_length_decider.clj) | Executable, sound dimension checking for finite signed matrices. |
| [`rainbow.math.linear.matrix.row-length-shape`](../src/rainbow/math/linear/matrix/row_length_shape.clj) | Bridges executable row-length evidence to abstract matrix shape certificates. |
| [`rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness`](../src/rainbow/math/linear/matrix/row_sum_fixed_point_uniqueness.clj) | Fixed-point uniqueness for row-sum-contractive signed affine systems. |
| [`rainbow.math.linear.matrix.row-sum-lipschitz`](../src/rainbow/math/linear/matrix/row_sum_lipschitz.clj) | Sup-Lipschitz bounds for nonnegative row-sum-bounded affine matrices. |
| [`rainbow.math.linear.matrix.shape`](../src/rainbow/math/linear/matrix/shape.clj) | Explicit width and rectangularity certificates for nested-List matrices. |
| [`rainbow.math.linear.matrix.signed-scale`](../src/rainbow/math/linear/matrix/signed_scale.clj) | Arbitrary signed-scalar homogeneity for native finite matrices. |
| [`rainbow.math.linear.matrix.signed-scale-algebra`](../src/rainbow/math/linear/matrix/signed_scale_algebra.clj) | Additivity and composition of arbitrary signed matrix scaling. |
| [`rainbow.math.linear.matrix.signed-scale-antitone`](../src/rainbow/math/linear/matrix/signed_scale_antitone.clj) | Nonpositive signed factors reverse scalar, vector, and matrix order. |
| [`rainbow.math.linear.matrix.signed-scale-congruence`](../src/rainbow/math/linear/matrix/signed_scale_congruence.clj) | Quotient congruence for signed scalar, vector, and matrix scaling. |
| [`rainbow.math.linear.matrix.signed-scale-order`](../src/rainbow/math/linear/matrix/signed_scale_order.clj) | Pointwise matrix order and monotonicity of signed module scaling. |
| [`rainbow.math.linear.matrix.signed-scale-positive`](../src/rainbow/math/linear/matrix/signed_scale_positive.clj) | Zero-value and nonnegativity laws for signed module scaling. |
| [`rainbow.math.linear.matrix.signed-scale-right`](../src/rainbow/math/linear/matrix/signed_scale_right.clj) | The complementary half of arbitrary signed matrix bilinearity. |
| [`rainbow.math.linear.matrix.signed-scale-sign`](../src/rainbow/math/linear/matrix/signed_scale_sign.clj) | The remaining sign combinations for signed scalar, vector, and matrix scaling. |
| [`rainbow.math.linear.matrix.signed-scale-subtract`](../src/rainbow/math/linear/matrix/signed_scale_subtract.clj) | Negation and subtraction laws for signed multiplication and module scaling. |
| [`rainbow.math.linear.matrix.signed-scale-units`](../src/rainbow/math/linear/matrix/signed_scale_units.clj) | Scalar-factor additivity and zero/one laws for signed matrix scaling. |
| [`rainbow.math.linear.matrix.subtract-linear`](../src/rainbow/math/linear/matrix/subtract_linear.clj) | Subtraction commutes with native matrix action, transpose, and products. |
| [`rainbow.math.linear.matrix.transpose`](../src/rainbow/math/linear/matrix/transpose.clj) | Total transpose primitives for row-major finite signed matrices. |
| [`rainbow.math.linear.matrix.transpose-equivalence`](../src/rainbow/math/linear/matrix/transpose_equivalence.clj) | Congruence laws for total native matrix transpose. |
| [`rainbow.math.linear.matrix.transpose-involution`](../src/rainbow/math/linear/matrix/transpose_involution.clj) | Algebraic foundations for nondegenerate transpose involution. |
| [`rainbow.math.linear.matrix.transpose-involution-positive`](../src/rainbow/math/linear/matrix/transpose_involution_positive.clj) | Transpose involution for rectangular matrices of positive width. |
| [`rainbow.math.linear.matrix.transpose-multiply`](../src/rainbow/math/linear/matrix/transpose_multiply.clj) | Transpose/product structure for nonempty native finite matrices. |
| [`rainbow.math.linear.matrix.transpose-multiply-reverse`](../src/rainbow/math/linear/matrix/transpose_multiply_reverse.clj) | Transpose reverses native matrix multiplication at positive width. |
| [`rainbow.math.linear.matrix.transpose-order`](../src/rainbow/math/linear/matrix/transpose_order.clj) | Pointwise order and nonnegativity for total native matrix transpose. |
| [`rainbow.math.linear.matrix.transpose-shape`](../src/rainbow/math/linear/matrix/transpose_shape.clj) | Rectangularity laws for total native matrix transpose. |

## Vectors (`src/rainbow/math/linear/vector/`, 44)

| namespace | |
|---|---|
| [`rainbow.math.linear.vector.add-cancellation`](../src/rainbow/math/linear/vector/add_cancellation.clj) | Shape-safe cancellation of a common vector from equivalence and order. |
| [`rainbow.math.linear.vector.add-order`](../src/rainbow/math/linear/vector/add_order.clj) | Translation monotonicity for native signed vectors. |
| [`rainbow.math.linear.vector.add-reorder`](../src/rainbow/math/linear/vector/add_reorder.clj) | Four-term reordering and additive distribution for vector subtraction. |
| [`rainbow.math.linear.vector.additive-units`](../src/rainbow/math/linear/vector/additive_units.clj) | Shape-preserving zero and additive-unit laws for native finite vectors. |
| [`rainbow.math.linear.vector.convex-combination`](../src/rainbow/math/linear/vector/convex_combination.clj) | Normalized two-point convex combinations preserve vector intervals. |
| [`rainbow.math.linear.vector.dot-additive`](../src/rainbow/math/linear/vector/dot_additive.clj) | Additivity of the native dot product in its first vector argument. |
| [`rainbow.math.linear.vector.dot-bilinear`](../src/rainbow/math/linear/vector/dot_bilinear.clj) | Right additivity of the native dot product, completing additive bilinearity. |
| [`rainbow.math.linear.vector.dot-commutative`](../src/rainbow/math/linear/vector/dot_commutative.clj) | Commutativity of the native truncating signed-vector dot product. |
| [`rainbow.math.linear.vector.dot-congruence`](../src/rainbow/math/linear/vector/dot_congruence.clj) | Quotient-safe congruence of the native vector dot product. |
| [`rainbow.math.linear.vector.dot-distance-bound`](../src/rainbow/math/linear/vector/dot_distance_bound.clj) | Componentwise distance accounting for signed dot products. |
| [`rainbow.math.linear.vector.dot-negate`](../src/rainbow/math/linear/vector/dot_negate.clj) | Negation laws for signed multiplication and the native vector dot product. |
| [`rainbow.math.linear.vector.dot-scale`](../src/rainbow/math/linear/vector/dot_scale.clj) | Homogeneity of the native vector dot product in its first argument. |
| [`rainbow.math.linear.vector.dot-subtract`](../src/rainbow/math/linear/vector/dot_subtract.clj) | Subtraction laws for signed values and the native vector dot product. |
| [`rainbow.math.linear.vector.dot-zero-laws`](../src/rainbow/math/linear/vector/dot_zero_laws.clj) | Zero laws for the native dot product and exact squared norm. |
| [`rainbow.math.linear.vector.equivalence`](../src/rainbow/math/linear/vector/equivalence.clj) | Componentwise equivalence of signed-rational vectors: two vectors are equivalent when every pair of components is signed-equivalent. |
| [`rainbow.math.linear.vector.equivalence-laws`](../src/rainbow/math/linear/vector/equivalence_laws.clj) | Structural laws for length-sensitive componentwise signed-vector equivalence. |
| [`rainbow.math.linear.vector.equivalence-transitivity`](../src/rainbow/math/linear/vector/equivalence_transitivity.clj) | Transitivity of length-sensitive componentwise vector equivalence. |
| [`rainbow.math.linear.vector.negate-additive`](../src/rainbow/math/linear/vector/negate_additive.clj) | Native vector negation distributes over native vector addition. |
| [`rainbow.math.linear.vector.negate-reflection`](../src/rainbow/math/linear/vector/negate_reflection.clj) | Involutive vector negation reflects order and equivalence. |
| [`rainbow.math.linear.vector.norm`](../src/rainbow/math/linear/vector/norm.clj) | The Euclidean vector norm over signed-rational vectors, built from the inner product and the perfect-square root witness: norm-squared v = <v, v> is-norm v n <=> n * n ~ <v, v> The squared norm is exact (a dot product);  |
| [`rainbow.math.linear.vector.norm-congruence`](../src/rainbow/math/linear/vector/norm_congruence.clj) | Quotient-safe congruence laws for native squared norms and norm witnesses. |
| [`rainbow.math.linear.vector.norm-expansion`](../src/rainbow/math/linear/vector/norm_expansion.clj) | Exact quadratic expansions for the native signed squared norm. |
| [`rainbow.math.linear.vector.norm-laws`](../src/rainbow/math/linear/vector/norm_laws.clj) | Algebraic laws for the exact signed squared norm. |
| [`rainbow.math.linear.vector.norm-nonnegative`](../src/rainbow/math/linear/vector/norm_nonnegative.clj) | Constructive nonnegativity of signed squares and native squared norms. |
| [`rainbow.math.linear.vector.norm-parallelogram`](../src/rainbow/math/linear/vector/norm_parallelogram.clj) | The exact parallelogram identity for native signed vectors. |
| [`rainbow.math.linear.vector.norm-pythagorean`](../src/rainbow/math/linear/vector/norm_pythagorean.clj) | Pythagoras and order bounds for native signed-rational vectors. |
| [`rainbow.math.linear.vector.norm-witness-laws`](../src/rainbow/math/linear/vector/norm_witness_laws.clj) | Transformation laws for exact native norm witnesses. |
| [`rainbow.math.linear.vector.norm-zero-characterization`](../src/rainbow/math/linear/vector/norm_zero_characterization.clj) | The proved forward zero-characterization for native exact norms. |
| [`rainbow.math.linear.vector.norm-zero-reflection`](../src/rainbow/math/linear/vector/norm_zero_reflection.clj) | Zero squared norm reflects componentwise zero for finite signed vectors. |
| [`rainbow.math.linear.vector.pointwise-order`](../src/rainbow/math/linear/vector/pointwise_order.clj) | Length-sensitive componentwise order for signed-rational vectors. |
| [`rainbow.math.linear.vector.pointwise-order-laws`](../src/rainbow/math/linear/vector/pointwise_order_laws.clj) | Partial-order laws and order-reversing negation for signed vectors. |
| [`rainbow.math.linear.vector.projected-gradient`](../src/rainbow/math/linear/vector/projected_gradient.clj) | Projected-gradient steps on finite signed-rational vectors. |
| [`rainbow.math.linear.vector.row-sum-lipschitz`](../src/rainbow/math/linear/vector/row_sum_lipschitz.clj) | Nonnegative row-sum Lipschitz bounds for signed dot products. |
| [`rainbow.math.linear.vector.scale-additive`](../src/rainbow/math/linear/vector/scale_additive.clj) | Uniform nonnegative scaling distributes over native vector addition. |
| [`rainbow.math.linear.vector.scale-composition`](../src/rainbow/math/linear/vector/scale_composition.clj) | Composition of uniform nonnegative scaling on native signed vectors. |
| [`rainbow.math.linear.vector.scale-order`](../src/rainbow/math/linear/vector/scale_order.clj) | Nonnegative-rational scaling preserves native positional vector order. |
| [`rainbow.math.linear.vector.scale-subtract`](../src/rainbow/math/linear/vector/scale_subtract.clj) | Uniform nonnegative scaling commutes with negation and subtraction. |
| [`rainbow.math.linear.vector.shape-add`](../src/rainbow/math/linear/vector/shape_add.clj) | Shape preservation for truncating vector addition and subtraction. |
| [`rainbow.math.linear.vector.shape-cancellation`](../src/rainbow/math/linear/vector/shape_cancellation.clj) | Shape equality and sound cancellation for truncating vector arithmetic. |
| [`rainbow.math.linear.vector.shape-map`](../src/rainbow/math/linear/vector/shape_map.clj) | Componentwise maps preserve native vector shape. |
| [`rainbow.math.linear.vector.subtract-cancellation`](../src/rainbow/math/linear/vector/subtract_cancellation.clj) | Shape-safe cancellation through native vector subtraction. |
| [`rainbow.math.linear.vector.subtract-laws`](../src/rainbow/math/linear/vector/subtract_laws.clj) | Congruence and mixed-variance order laws for native vector subtraction. |
| [`rainbow.math.linear.vector.subtract-negation`](../src/rainbow/math/linear/vector/subtract_negation.clj) | Interaction laws between native vector subtraction and negation. |
| [`rainbow.math.linear.vector.uniform-clamp`](../src/rainbow/math/linear/vector/uniform_clamp.clj) | Uniform box projection for finite signed-rational vectors. |

## Logic (`src/rainbow/math/logic/`, 16)

| namespace | |
|---|---|
| [`rainbow.math.logic.boolean-and`](../src/rainbow/math/logic/boolean_and.clj) | General soundness of the boolean AND used across the AHoF membership/monitor rows (interval containment, 2-D ODD boxes, polytope halfspaces, ...): and a b = if a then b else false (a Bool.rec over the first operand) Prov |
| [`rainbow.math.logic.clamp-range`](../src/rainbow/math/logic/clamp_range.clj) | Universal correctness of clamping (the PPO / trust-region clip of AHoF D52), built on the general nnrat min/max bounds: clamp r lo hi = min (max r lo) hi Proved for ALL r, lo, hi (not just worked instances): clamp-at-mos |
| [`rainbow.math.logic.exhaustive-carrier-fintype`](../src/rainbow/math/logic/exhaustive_carrier_fintype.clj) | Constructively connect executable exhaustive carriers to extensional Fintype. |
| [`rainbow.math.logic.finset`](../src/rainbow/math/logic/finset.clj) | Extensional bundled finite sets as native Clojure proof data. |
| [`rainbow.math.logic.fintype`](../src/rainbow/math/logic/fintype.clj) | Finite carrier data as an extensional complete native Finset. |
| [`rainbow.math.logic.function-predicate`](../src/rainbow/math/logic/function_predicate.clj) | Checked native declarations for reusable higher-order function predicates. |
| [`rainbow.math.logic.half-monotone`](../src/rainbow/math/logic/half_monotone.clj) | The general halving-monotonicity lemma for the convergence capstone: (1/2) * d <= d for every nonnegative rational d. |
| [`rainbow.math.logic.infinite-injection`](../src/rainbow/math/logic/infinite_injection.clj) | Classical, sort-polymorphic infinitude transport along injections. |
| [`rainbow.math.logic.infinite-transport`](../src/rainbow/math/logic/infinite_transport.clj) | Sort-polymorphic infinitude transport and a faithful native Int model. |
| [`rainbow.math.logic.interval-membership-sound`](../src/rainbow/math/logic/interval_membership_sound.clj) | Universal soundness of the two-clause interval/box membership test, composing the general boolean-AND soundness (rainbow.math.logic.boolean-and) with the decidable order: contains? |
| [`rainbow.math.logic.maximum-expected-utility`](../src/rainbow/math/logic/maximum_expected_utility.clj) | AHoF D17: finite exact-rational maximum expected utility. |
| [`rainbow.math.logic.proof-irrelevance`](../src/rainbow/math/logic/proof_irrelevance.clj) | Proof irrelevance from propositional extensionality. |
| [`rainbow.math.logic.scan-correctness`](../src/rainbow/math/logic/scan_correctness.clj) | GENERAL (abstract-element) correctness theorems for the prefix-sum scan: for arbitrary list elements a, b, c the running totals are exactly the prefix sums, cumulative-sum [a] = [a] cumulative-sum [a, b] = [a, a + b] cum |
| [`rainbow.math.logic.scan-length`](../src/rainbow/math/logic/scan_length.clj) | A GENERAL (for-all-inputs) correctness theorem about the prefix-sum scan: scanning a list preserves its length, length (cumulative-sum xs) = length xs for every list xs. |
| [`rainbow.math.logic.strict-contraction-stabilization`](../src/rainbow/math/logic/strict_contraction_stabilization.clj) | Constructive bounded stabilization of strict contractions in a finite Nat sup metric. |
| [`rainbow.math.logic.strict-contraction-uniqueness`](../src/rainbow/math/logic/strict_contraction_uniqueness.clj) | Constructive uniqueness of support-relative fixed points for strict finite contractions. |

## Natural numbers (`src/rainbow/math/nat/`, 29)

| namespace | |
|---|---|
| [`rainbow.math.nat.add-order`](../src/rainbow/math/nat/add_order.clj) | Additive monotonicity building blocks for the convergence proof: a natural number is at most itself plus anything, and in particular at most its own double. |
| [`rainbow.math.nat.at-most-add`](../src/rainbow/math/nat/at_most_add.clj) | Three one-line order facts about addition that the program-family index arithmetic keeps needing (nat/at-most a b unfolds to exists e, a + e = b; addition recurses on its LEFT argument, so `a <= a + b` is a direct witnes |
| [`rainbow.math.nat.at-most-cancellation`](../src/rainbow/math/nat/at_most_cancellation.clj) | Real-analysis bedrock (roadmap step 1): cancellation for the nat order. |
| [`rainbow.math.nat.contraction`](../src/rainbow/math/nat/contraction.clj) | Natural multiplication laws needed by finite metric contraction proofs. |
| [`rainbow.math.nat.distance`](../src/rainbow/math/nat/distance.clj) | Computational natural distance and additive foreign-vocabulary bridges. |
| [`rainbow.math.nat.distance-core`](../src/rainbow/math/nat/distance_core.clj) | Constructive zero and identity laws for computational natural distance. |
| [`rainbow.math.nat.distance-radius`](../src/rainbow/math/nat/distance_radius.clj) | Natural distance is the least symmetric additive radius. |
| [`rainbow.math.nat.distributive`](../src/rainbow/math/nat/distributive.clj) | Left-distributivity of nat multiplication over addition: a * (b + c) = a * b + a * c for all a, b, c, the semiring law missing from nat_semiring (which has associativity, commutativity of addition, multiply-one-right, bu |
| [`rainbow.math.nat.divisibility`](../src/rainbow/math/nat/divisibility.clj) | Native natural-number divisibility for arithmetic proof interfaces. |
| [`rainbow.math.nat.divmod`](../src/rainbow/math/nat/divmod.clj) | Row/column of a FLAT PAIR INDEX, kernel-side, with the bounds the pair-vector families need (Floyd-Warshall's round is a block of n*n components indexed by c = col + row*n). |
| [`rainbow.math.nat.extremal-index`](../src/rainbow/math/nat/extremal_index.clj) | LEAST AND GREATEST WITNESSES of a decidable predicate on 0..k, constructively (for the Floyd-Warshall invariant: the first and last intermediate visit of the new pivot). |
| [`rainbow.math.nat.infinite`](../src/rainbow/math/nat/infinite.clj) | Axiom-free Nat constructor discrimination, list bounds, and infinitude. |
| [`rainbow.math.nat.linear-order`](../src/rainbow/math/nat/linear_order.clj) | Executable decision data, min/max, and three-way comparison for Nat. |
| [`rainbow.math.nat.metric`](../src/rainbow/math/nat/metric.clj) | Constructive order laws for computational natural distance. |
| [`rainbow.math.nat.metric-separation`](../src/rainbow/math/nat/metric_separation.clj) | Constructive positivity and separation laws for computational Nat distance. |
| [`rainbow.math.nat.monus`](../src/rainbow/math/nat/monus.clj) | Truncated subtraction on Nat (monus), the missing arithmetic primitive under the signed->nnrat magnitude foundation. |
| [`rainbow.math.nat.multiply-positive`](../src/rainbow/math/nat/multiply_positive.clj) | Constructive nat positivity of a product: 0 < a -> 0 < b -> 0 < a*b (strict-below form). |
| [`rainbow.math.nat.multiply-zero-split`](../src/rainbow/math/nat/multiply_zero_split.clj) | nat/multiply-zero-split : a*b = 0 -> (a = 0) or (b = 0). |
| [`rainbow.math.nat.order`](../src/rainbow/math/nat/order.clj) | Constructive monotonicity for Nat arithmetic and finite expectation. |
| [`rainbow.math.nat.pair-index-inverse`](../src/rainbow/math/nat/pair_index_inverse.clj) | INVERTING THE PAIR INDEX. |
| [`rainbow.math.nat.pigeonhole`](../src/rainbow/math/nat/pigeonhole.clj) | THE PIGEONHOLE PRINCIPLE ON NAT, constructively. |
| [`rainbow.math.nat.power`](../src/rainbow/math/nat/power.clj) | Natural-number exponentiation base^exp, defined by recursion on the exponent: power b 0 = 1 power b (succ e) = b * (power b e). |
| [`rainbow.math.nat.power-growth`](../src/rainbow/math/nat/power_growth.clj) | Growth lemmas for nat exponentiation, on the road to the geometric-convergence modulus. |
| [`rainbow.math.nat.ring-reflect`](../src/rainbow/math/nat/ring_reflect.clj) | Definitions for proving nat semiring identities BY REFLECTION. |
| [`rainbow.math.nat.ring-reflect-sound`](../src/rainbow/math/nat/ring_reflect_sound.clj) | Unconditional, native soundness of the nat reflection normalizer. |
| [`rainbow.math.nat.semiring`](../src/rainbow/math/nat/semiring.clj) | Constructive natural semiring laws needed by rational proof data. |
| [`rainbow.math.nat.square-zero`](../src/rainbow/math/nat/square_zero.clj) | nat/square-zero-implies-zero : a*a = 0 -> a = 0. |
| [`rainbow.math.nat.strict-below-more`](../src/rainbow/math/nat/strict_below_more.clj) | Small reusable nat lemmas for indexed-fold attainment (pure nat, off the trusted base): nat/add-successor-right : i + succ e = succ (i + e) (add recurses left, so this needs proof) nat/strict-below-self : m < succ m nat/ |
| [`rainbow.math.nat.strict-below-split`](../src/rainbow/math/nat/strict_below_split.clj) | nat/strict-below-successor-split : strict-below i (succ m) -> (strict-below i m) or (i = m). |

## Rationals (`src/rainbow/math/rational/`, 4)

| namespace | |
|---|---|
| [`rainbow.math.rational.bellman`](../src/rainbow/math/rational/bellman.clj) | Finite fixed-policy Bellman evaluation over nonnegative rational proof data. |
| [`rainbow.math.rational.convergence`](../src/rainbow/math/rational/convergence.clj) | Convergence of a nonnegative-rational distance sequence to its limit, with an explicit rational modulus -- the analysis layer above the geometric contraction bound. |
| [`rainbow.math.rational.division`](../src/rainbow/math/rational/division.clj) | Exact division of nonnegative rationals. |
| [`rainbow.math.rational.value`](../src/rainbow/math/rational/value.clj) | Exact nonnegative-rational worked values, proven through cross-product equivalence rather than pair equality. |

## Binary numerals (`src/rainbow/math/rational/binary/`, 2)

| namespace | |
|---|---|
| [`rainbow.math.rational.binary.rational-order`](../src/rainbow/math/rational/binary/rational_order.clj) | Brick 5b of the binary-numeral roadmap: a Bin-NATIVE rational comparison, proved to agree with the trusted checker's rational decision `audit/decide-nnrat-at-most`. |
| [`rainbow.math.rational.binary.signed-order`](../src/rainbow/math/rational/binary/signed_order.clj) | The SIGNED bridge: the checker's actual hot decision `signed/decide-at-most` on the Bin layer, proved to agree with -- and to entail the soundness of -- the trusted signed order. |

## Non-negative rationals (`src/rainbow/math/rational/nnrat/`, 140)

| namespace | |
|---|---|
| [`rainbow.math.rational.nnrat.add-cancel-zero`](../src/rainbow/math/rational/nnrat/add_cancel_zero.clj) | Additive cancellation to zero for nonnegative rationals: nnrat/add-cancel-to-zero : (a + g) ~ a -> g ~ 0 If adding g changes nothing, g was 0. |
| [`rainbow.math.rational.nnrat.add-cancellation`](../src/rainbow/math/rational/nnrat/add_cancellation.clj) | Real-analysis roadmap step 3: additive cancellation for the nnrat order -- nnrat/at-most-add-right-cancel : (X + k) <= (Y + k) -> X <= Y the converse of add-monotonicity, and the piece signed order transitivity needs (it |
| [`rainbow.math.rational.nnrat.add-monotone`](../src/rainbow/math/rational/nnrat/add_monotone.clj) | Universal (one-sided) monotonicity of nonnegative-rational addition under the rational order -- the additive companion to nnrat/multiply-monotone, and the keystone for convex-combination / weighted-average bounds: add-ri |
| [`rainbow.math.rational.nnrat.add-upper`](../src/rainbow/math/rational/nnrat/add_upper.clj) | The additive upper-bound law: a nonnegative rational is at most itself plus anything, `a <= a + b`. |
| [`rainbow.math.rational.nnrat.add-zero-split`](../src/rainbow/math/rational/nnrat/add_zero_split.clj) | Nonnegativity forces zero: for nonnegative rationals, a sum equivalent to 0 forces each summand to 0. |
| [`rainbow.math.rational.nnrat.additive-reassociation`](../src/rainbow/math/rational/nnrat/additive_reassociation.clj) | Associativity and reusable summand reorder laws for native nonnegative rationals. |
| [`rainbow.math.rational.nnrat.archimedean`](../src/rainbow/math/rational/nnrat/archimedean.clj) | The Archimedean reciprocal limit helper for nonnegative rationals. |
| [`rainbow.math.rational.nnrat.commutative`](../src/rainbow/math/rational/nnrat/commutative.clj) | Native commutativity of nonnegative-rational addition and multiplication, up to cross-multiplication equivalence. |
| [`rainbow.math.rational.nnrat.complement-proper`](../src/rainbow/math/rational/nnrat/complement_proper.clj) | Proper raw fraction for the exact complement of a positive subunit mass. |
| [`rainbow.math.rational.nnrat.contraction-general`](../src/rainbow/math/rational/nnrat/contraction_general.clj) | Generalized contraction convergence: ANY contraction rate gamma <= 1/2 drives the error to zero. |
| [`rainbow.math.rational.nnrat.contraction-uniqueness`](../src/rainbow/math/rational/nnrat/contraction_uniqueness.clj) | Banach fixed-point UNIQUENESS, the collapse half (the convergence half is nnrat-general-contraction). |
| [`rainbow.math.rational.nnrat.convex`](../src/rainbow/math/rational/nnrat/convex.clj) | The convex-combination bound -- the capstone of the nnrat monotonicity + algebra foundation: convex-at-most-max : (w0 + w1) ~ 1 -> w0*v0 + w1*v1 <= max v0 v1 (all w0 w1 v0 v1) A weighted average with weights summing to o |
| [`rainbow.math.rational.nnrat.convex-multi-point`](../src/rainbow/math/rational/nnrat/convex_multi_point.clj) | Finite nonnegative-weighted combinations preserve global value bounds: sum_i (w i * m) <= sum_i (w i * v i) when forall i, m <= v i sum_i (w i * v i) <= sum_i (w i * Mx) when forall i, v i <= Mx These are the N-point con |
| [`rainbow.math.rational.nnrat.convex-normalized`](../src/rainbow/math/rational/nnrat/convex_normalized.clj) | The normalized two-point convex bracket over nonnegative rationals. |
| [`rainbow.math.rational.nnrat.convex-two-point`](../src/rainbow/math/rational/nnrat/convex_two_point.clj) | The unnormalized two-point convex-combination bracket over nonnegative rationals: (w0+w1)*min(v0,v1) <= w0*v0+w1*v1 <= (w0+w1)*max(v0,v1) The weights are arbitrary nonnegative rationals; they need not sum to one. |
| [`rainbow.math.rational.nnrat.diagonal-spike`](../src/rainbow/math/rational/nnrat/diagonal_spike.clj) | Canonical exact-rational diagonal spikes over duplicate-free finite carriers. |
| [`rainbow.math.rational.nnrat.distance`](../src/rainbow/math/rational/nnrat/distance.clj) | A quotient-safe computational distance on exact nonnegative rationals. |
| [`rainbow.math.rational.nnrat.distance-translation`](../src/rainbow/math/rational/nnrat/distance_translation.clj) | Removing common nonnegative mass preserves exact rational distance. |
| [`rainbow.math.rational.nnrat.distribute-right`](../src/rainbow/math/rational/nnrat/distribute_right.clj) | Right-distributivity of nonnegative-rational multiplication over addition, carrying ONLY that law. |
| [`rainbow.math.rational.nnrat.distributive`](../src/rainbow/math/rational/nnrat/distributive.clj) | Right-distributivity of nonnegative-rational multiplication over addition, up to nnrat equivalence: multiply-distributes-add-right : (a + b) * m ~ a*m + b*m (all a b m) This is the last algebra brick for the convex-combi |
| [`rainbow.math.rational.nnrat.farkas-additive-cross`](../src/rainbow/math/rational/nnrat/farkas_additive_cross.clj) | Brick 5c core of the general LP strong-duality Fourier-Motzkin encoding : the additive cross-elimination crux -- the necessary (certificate) direction, coefficient-1 case. |
| [`rainbow.math.rational.nnrat.farkas-affine-cross`](../src/rainbow/math/rational/nnrat/farkas_affine_cross.clj) | Brick 5c full of the general LP strong-duality Fourier-Motzkin encoding : the affine cross-elimination crux WITH COEFFICIENTS -- the coefficient wrapper around the additive core. |
| [`rainbow.math.rational.nnrat.farkas-alternative`](../src/rainbow/math/rational/nnrat/farkas_alternative.clj) | Constructive Farkas alternative for arbitrary finite nnrat elimination chains. |
| [`rainbow.math.rational.nnrat.farkas-both-sides`](../src/rainbow/math/rational/nnrat/farkas_both_sides.clj) | Brick 5d-ii of the general LP strong-duality Fourier-Motzkin encoding : converting a both-sides row into a clean affine lower row, subtraction-free. |
| [`rainbow.math.rational.nnrat.farkas-both-sides-reduce`](../src/rainbow/math/rational/nnrat/farkas_both_sides_reduce.clj) | Recursive-reduction sub-brick of brick 6 (single-row core): reduce a both-sides cross row to an affine row in the surviving variable. |
| [`rainbow.math.rational.nnrat.farkas-bridge-list`](../src/rainbow/math/rational/nnrat/farkas_bridge_list.clj) | Piece 1 of the n-variable capstone: the bridge-mapping -- map the structured bridge over a list of cross rows. |
| [`rainbow.math.rational.nnrat.farkas-cross-bilist`](../src/rainbow/math/rational/nnrat/farkas_cross_bilist.clj) | Brick 6 (cross-product core) of the general LP strong-duality Fourier-Motzkin encoding: the cross-product over BOTH row lists -- a list of affine lower rows against a list of affine upper rows. |
| [`rainbow.math.rational.nnrat.farkas-cross-bridge`](../src/rainbow/math/rational/nnrat/farkas_cross_bridge.clj) | Piece 1 core of the n-variable capstone: the structured bridge recognizing a cross condition as a both-sides row. |
| [`rainbow.math.rational.nnrat.farkas-cross-list`](../src/rainbow/math/rational/nnrat/farkas_cross_list.clj) | Brick 5d-i of the general LP strong-duality Fourier-Motzkin encoding : the cross-product of one affine lower row against a LIST of affine upper rows. |
| [`rainbow.math.rational.nnrat.farkas-cross-vectors`](../src/rainbow/math/rational/nnrat/farkas_cross_vectors.clj) | The unified representation, brick 3 core: one elimination cross at the coefficient-vector level. |
| [`rainbow.math.rational.nnrat.farkas-cross-vectors-bilist`](../src/rainbow/math/rational/nnrat/farkas_cross_vectors_bilist.clj) | Brick 3 full round: cross a LIST of lower coefficient-vector constraints against a LIST of upper coefficient-vector constraints -- the whole round's reduced set. |
| [`rainbow.math.rational.nnrat.farkas-cross-vectors-list`](../src/rainbow/math/rational/nnrat/farkas_cross_vectors_list.clj) | Brick 3 per-pair fold: cross one lower coefficient-vector constraint against a LIST of upper coefficient-vector constraints. |
| [`rainbow.math.rational.nnrat.farkas-elim`](../src/rainbow/math/rational/nnrat/farkas_elim.clj) | A bounded first Fourier--Motzkin milestone over exact nonnegative rationals. |
| [`rainbow.math.rational.nnrat.farkas-elim-affine-coupled`](../src/rainbow/math/rational/nnrat/farkas_elim_affine_coupled.clj) | Brick 3 of the general LP strong-duality Fourier-Motzkin encoding : elimination of an nnrat variable v whose upper coupling carries an additive SURVIVOR-SUM term. |
| [`rainbow.math.rational.nnrat.farkas-elim-affine-decidable`](../src/rainbow/math/rational/nnrat/farkas_elim_affine_decidable.clj) | Brick 4b of the general LP strong-duality Fourier-Motzkin encoding : decidability of the one-variable affine-list elimination -- the Farkas-alternative half. |
| [`rainbow.math.rational.nnrat.farkas-elim-affine-list`](../src/rainbow/math/rational/nnrat/farkas_elim_affine_list.clj) | Brick 4 of the general LP strong-duality Fourier-Motzkin encoding : the one-primal-variable FM elimination step over a LIST of affine upper rows -- the first genuinely new formalization of the lane. |
| [`rainbow.math.rational.nnrat.farkas-elim-affine-list-lower`](../src/rainbow/math/rational/nnrat/farkas_elim_affine_list_lower.clj) | Brick 5b of the general LP strong-duality Fourier-Motzkin encoding : the one-variable elimination step over a list of affine LOWER rows -- the mirror of brick 4 (nnrat_farkas_elim_affine_list.clj) for the other bound dir |
| [`rainbow.math.rational.nnrat.farkas-elim-chain`](../src/rainbow/math/rational/nnrat/farkas_elim_chain.clj) | Arbitrary finite chains of constructive nnrat Fourier--Motzkin steps. |
| [`rainbow.math.rational.nnrat.farkas-elim-coupled`](../src/rainbow/math/rational/nnrat/farkas_elim_coupled.clj) | Constructive elimination of an nnrat variable coupled to a survivor. |
| [`rainbow.math.rational.nnrat.farkas-elim-list`](../src/rainbow/math/rational/nnrat/farkas_elim_list.clj) | List-sized one-variable Fourier--Motzkin elimination over nnrat bounds. |
| [`rainbow.math.rational.nnrat.farkas-elim-scaled-coupled`](../src/rainbow/math/rational/nnrat/farkas_elim_scaled_coupled.clj) | Brick 1 of the general LP strong-duality Fourier-Motzkin encoding : elimination of an nnrat variable v that appears with a COEFFICIENT in its coupling to a survivor. |
| [`rainbow.math.rational.nnrat.farkas-elim-scaled-coupled-lower`](../src/rainbow/math/rational/nnrat/farkas_elim_scaled_coupled_lower.clj) | Brick 2 of the general LP strong-duality Fourier-Motzkin encoding : elimination of an nnrat variable v whose coupling to a survivor is a scaled LOWER bound. |
| [`rainbow.math.rational.nnrat.farkas-elim-two-var`](../src/rainbow/math/rational/nnrat/farkas_elim_two_var.clj) | Constructive composition of list-sized elimination for two decoupled nnrat variables. |
| [`rainbow.math.rational.nnrat.farkas-eliminate-all`](../src/rainbow/math/rational/nnrat/farkas_eliminate_all.clj) | The over-variable recursion: iterate one elimination round over the variable count. |
| [`rainbow.math.rational.nnrat.farkas-eliminate-base`](../src/rainbow/math/rational/nnrat/farkas_eliminate_base.clj) | The over-variable recursion's base case: a fully-reduced constraint is a constant comparison. |
| [`rainbow.math.rational.nnrat.farkas-eliminate-round`](../src/rainbow/math/rational/nnrat/farkas_eliminate_round.clj) | One full Fourier-Motzkin elimination round, composed : cross-product then reduction. |
| [`rainbow.math.rational.nnrat.farkas-form-scale`](../src/rainbow/math/rational/nnrat/farkas_form_scale.clj) | The unified representation, brick 2 core: scaling a linear form scales its coefficient vector. |
| [`rainbow.math.rational.nnrat.farkas-linear-form`](../src/rainbow/math/rational/nnrat/farkas_linear_form.clj) | The unified representation, brick 1: the coefficient-vector (linear-form) constraint type and the head-split extraction. |
| [`rainbow.math.rational.nnrat.farkas-partition-covered`](../src/rainbow/math/rational/nnrat/farkas_partition_covered.clj) | The vacuity FIX for the partition keystone: farkas-partition-list-necessary strengthened with a COVERING conjunct that ties the output partition to the input, killing the empty witness. |
| [`rainbow.math.rational.nnrat.farkas-partition-list`](../src/rainbow/math/rational/nnrat/farkas_partition_list.clj) | Piece (ii) brick 1: the dependent partition of a reduced disjunction system into a lower-list and an upper-list. |
| [`rainbow.math.rational.nnrat.farkas-partition-row`](../src/rainbow/math/rational/nnrat/farkas_partition_row.clj) | Piece (ii) brick 1 core: the per-row step of the dependent partition. |
| [`rainbow.math.rational.nnrat.farkas-recursion-step`](../src/rainbow/math/rational/nnrat/farkas_recursion_step.clj) | Piece (ii) recursion step: one full elimination round yields a feasible reduced lower/upper system. |
| [`rainbow.math.rational.nnrat.farkas-recursion-step-covered`](../src/rainbow/math/rational/nnrat/farkas_recursion_step_covered.clj) | Covered recursion step (the vacuity fix, consumer migration): the affine elimination round built on the COVERING-strengthened partition keystone. |
| [`rainbow.math.rational.nnrat.farkas-reduce-align`](../src/rainbow/math/rational/nnrat/farkas_reduce_align.clj) | Piece (i) of the n-variable capstone: the data-representation alignment that lets the elimination round close on structured cross rows. |
| [`rainbow.math.rational.nnrat.farkas-reduce-list`](../src/rainbow/math/rational/nnrat/farkas_reduce_list.clj) | Recursive-reduction sub-brick of brick 6 (list form): map the single-row reduction over a list of both-sides cross rows. |
| [`rainbow.math.rational.nnrat.farkas-reduced-list-satisfied`](../src/rainbow/math/rational/nnrat/farkas_reduced_list_satisfied.clj) | Farkas elimination REDUCTION CORRECTNESS (the SUFFICIENCY direction): nnrat/farkas-reduced-list-satisfied : forall rows w, farkas-reduced-conditions rows w -> farkas-both-sides-rows-satisfied rows w The existing forward  |
| [`rainbow.math.rational.nnrat.farkas-reduced-vector`](../src/rainbow/math/rational/nnrat/farkas_reduced_vector.clj) | The unified representation, brick 2 assembly : the cross condition expressed as a both-sides constraint over transformed coefficient vectors. |
| [`rainbow.math.rational.nnrat.farkas-row-reconstruction`](../src/rainbow/math/rational/nnrat/farkas_row_reconstruction.clj) | Reconstruct a source inequality from its reduced affine row and coefficient equation. |
| [`rainbow.math.rational.nnrat.farkas-row-repackage`](../src/rainbow/math/rational/nnrat/farkas_row_repackage.clj) | Brick 5a of the general LP strong-duality Fourier-Motzkin encoding : the row-repackaging crux, the one genuinely new proof obligation of the strong-duality payoff. |
| [`rainbow.math.rational.nnrat.farkas-vector-adapter-bilist`](../src/rainbow/math/rational/nnrat/farkas_vector_adapter_bilist.clj) | The unified representation, partition bridge adapter (the bilist) : turn one whole elimination round's reduced conditions into the flat descriptor fold the bridge consumes. |
| [`rainbow.math.rational.nnrat.farkas-vector-adapter-list`](../src/rainbow/math/rational/nnrat/farkas_vector_adapter_list.clj) | The unified representation, partition bridge adapter (per-upper list) : turn one round's per-lower reduced conditions into the flat descriptor fold the bridge consumes. |
| [`rainbow.math.rational.nnrat.farkas-vector-both-sides`](../src/rainbow/math/rational/nnrat/farkas_vector_both_sides.clj) | The unified representation, second-variable step: convert a reduced both-sides COEFFICIENT-VECTOR row into a lower/upper affine row in the next variable x2, subtraction-free. |
| [`rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce`](../src/rainbow/math/rational/nnrat/farkas_vector_both_sides_reduce.clj) | The unified representation, per-row reduction: reduce a both-sides COEFFICIENT-VECTOR row to a lower/upper affine row in the next variable x2 -- as a disjunction, ready for the partition. |
| [`rainbow.math.rational.nnrat.farkas-vector-partition-fold`](../src/rainbow/math/rational/nnrat/farkas_vector_partition_fold.clj) | The unified representation, partition bridge (the fold) : collect a LIST of reduced coefficient-vector rows into the affine partition's input. |
| [`rainbow.math.rational.nnrat.farkas-vector-partition-pack`](../src/rainbow/math/rational/nnrat/farkas_vector_partition_pack.clj) | The unified representation, partition bridge (single row) : pack one reduced coefficient-vector row into a both-sides DATA row and discharge its reduced-conditions entry. |
| [`rainbow.math.rational.nnrat.farkas-vector-round`](../src/rainbow/math/rational/nnrat/farkas_vector_round.clj) | The unified representation, one closed round: a feasible coefficient-vector system in k+1 variables yields a feasible affine system in k variables. |
| [`rainbow.math.rational.nnrat.farkas-vector-round-covered`](../src/rainbow/math/rational/nnrat/farkas_vector_round_covered.clj) | Covered coefficient-vector round (the vacuity fix, consumer migration): one Fourier-Motzkin round on the covering-strengthened partition keystone. |
| [`rainbow.math.rational.nnrat.farkas-vector-step`](../src/rainbow/math/rational/nnrat/farkas_vector_step.clj) | The unified representation, the recursion step: one closed elimination step in the held next-variable representation, and its instantiation of the over-variable recursion skeleton. |
| [`rainbow.math.rational.nnrat.farkas-vector-step-covered`](../src/rainbow/math/rational/nnrat/farkas_vector_step_covered.clj) | Covered elimination step (the vacuity fix, consumer migration): one step in the held next-variable representation carrying the covering conjunct. |
| [`rainbow.math.rational.nnrat.farkas-vector-unit-column`](../src/rainbow/math/rational/nnrat/farkas_vector_unit_column.clj) | The unified representation, unit-column re-presentation : re-present a round's affine output rows as next-variable coefficient constraints, so the round's output feeds its own input and successive rounds chain. |
| [`rainbow.math.rational.nnrat.farkas-vector-unit-repr-length`](../src/rainbow/math/rational/nnrat/farkas_vector_unit_repr_length.clj) | Length preservation of the unit-column re-presentation map (support for the covered step migration). |
| [`rainbow.math.rational.nnrat.finite-min-positive`](../src/rainbow/math/rational/nnrat/finite_min_positive.clj) | Positive lower bounds from finite exact-rational minima. |
| [`rainbow.math.rational.nnrat.fubini`](../src/rainbow/math/rational/nnrat/fubini.clj) | Fubini / double-sum swap for finite nnrat sums, up to nnrat equivalence (~): nnrat/map-sum-swap : sum_{i in is} sum_{j in js} F i j ~ sum_{j in js} sum_{i in is} F i j i.e. |
| [`rainbow.math.rational.nnrat.general-contraction`](../src/rainbow/math/rational/nnrat/general_contraction.clj) | Arbitrary-gamma contraction convergence. |
| [`rainbow.math.rational.nnrat.general-harmonic`](../src/rainbow/math/rational/nnrat/general_harmonic.clj) | General harmonic null sequence, the bound that dominates any contraction rate gamma<1: nnrat/general-harmonic ap gp n := a / (a + n*g) with a = ap+1, g = gp+1 analysis/general-harmonic-null : rate-null (general-harmonic  |
| [`rainbow.math.rational.nnrat.geometric-convergence`](../src/rainbow/math/rational/nnrat/geometric_convergence.clj) | The geometric (contraction-rate) convergence payoff, fully self-contained: the sequence (1/2)^n converges to zero. |
| [`rainbow.math.rational.nnrat.half-positive`](../src/rainbow/math/rational/nnrat/half_positive.clj) | nnrat/half-positive : 0 < half (as the reducible conjunction 0<=half AND not(0~half)). |
| [`rainbow.math.rational.nnrat.harmonic-convergence`](../src/rainbow/math/rational/nnrat/harmonic_convergence.clj) | A CONCRETE convergence theorem: the harmonic sequence 1/(n+1) converges to zero, with an explicit modulus. |
| [`rainbow.math.rational.nnrat.identities`](../src/rainbow/math/rational/nnrat/identities.clj) | Neutral and absorbing laws for native nonnegative rationals, up to cross-product equivalence. |
| [`rainbow.math.rational.nnrat.inverse-gap-certificate`](../src/rainbow/math/rational/nnrat/inverse_gap_certificate.clj) | Sharp inverse-gap residual arithmetic directly in NNRAT. |
| [`rainbow.math.rational.nnrat.lattice-monotone`](../src/rainbow/math/rational/nnrat/lattice_monotone.clj) | Universal monotonicity of the exact-rational min and max under the rational order, composing the min/max bound + lattice-step theorems from rainbow.math.rational.nnrat.minmax: min-monotone : a<=a' -> b<=b' -> min a b <=  |
| [`rainbow.math.rational.nnrat.list-sum`](../src/rainbow/math/rational/nnrat/list_sum.clj) | Finite sum of an nnrat-valued map over a list, and its monotonicity -- the n-ary generalization of nnrat/wsum2-monotone and the fold-level induction the scout flagged as the missing piece for dot-product / LP bounds: nnr |
| [`rainbow.math.rational.nnrat.lp-complementary`](../src/rainbow/math/rational/nnrat/lp_complementary.clj) | Complementary slackness for LP over nonnegative rationals -- the KKT optimality characterization, now a named machine-checked theorem. |
| [`rainbow.math.rational.nnrat.lp-example`](../src/rainbow/math/rational/nnrat/lp_example.clj) | A concrete, fully worked LP with a machine-checked optimality certificate -- the tangible 'sellable' artifact: a real optimization instance whose proposed solution is PROVEN optimal by the kernel, with no trust in any so |
| [`rainbow.math.rational.nnrat.lp-gap`](../src/rainbow/math/rational/nnrat/lp_gap.clj) | LP duality-gap decomposition over nonnegative rationals -- the identity behind complementary slackness. |
| [`rainbow.math.rational.nnrat.lp-multi-constraint-duality`](../src/rainbow/math/rational/nnrat/lp_multi_constraint_duality.clj) | Finite positive-constraint, one-variable LP duality over nnrat. |
| [`rainbow.math.rational.nnrat.lp-optimality`](../src/rainbow/math/rational/nnrat/lp_optimality.clj) | LP optimality certificate over nonnegative rationals -- the sellable corollary of weak duality: a matching feasible primal/dual pair PROVES optimality. |
| [`rainbow.math.rational.nnrat.lp-separable-multi-var`](../src/rainbow/math/rational/nnrat/lp_separable_multi_var.clj) | Zero total duality gap for a finite list of decoupled scalar nnrat LPs. |
| [`rainbow.math.rational.nnrat.lp-separable-two-var`](../src/rainbow/math/rational/nnrat/lp_separable_two_var.clj) | Strong duality for the sum of two decoupled scalar nnrat LPs. |
| [`rainbow.math.rational.nnrat.lp-strong-duality`](../src/rainbow/math/rational/nnrat/lp_strong_duality.clj) | Concrete textbook strong duality for a verified Bool-indexed 2x2 LP. |
| [`rainbow.math.rational.nnrat.lp-strong-duality-general`](../src/rainbow/math/rational/nnrat/lp_strong_duality_general.clj) | Constructive strong duality for a parametric scalar LP. |
| [`rainbow.math.rational.nnrat.lp-two-var-strong-duality`](../src/rainbow/math/rational/nnrat/lp_two_var_strong_duality.clj) | Brick 5d-iii of the general LP strong-duality Fourier-Motzkin encoding : a two-variable strong-duality instance whose primal-optimality is proved BY THE FM ENGINE. |
| [`rainbow.math.rational.nnrat.lp-weak-duality`](../src/rainbow/math/rational/nnrat/lp_weak_duality.clj) | LP weak duality over nonnegative rationals -- the frontier-OR capstone: primal max c.x s.t. |
| [`rainbow.math.rational.nnrat.map-sum-additive`](../src/rainbow/math/rational/nnrat/map_sum_additive.clj) | Additive congruences for nnrat/map-sum, up to nnrat equivalence (~) -- the Fubini prerequisites. |
| [`rainbow.math.rational.nnrat.map-sum-append`](../src/rainbow/math/rational/nnrat/map_sum_append.clj) | Finite nnrat sums split over list concatenation, up to nnrat equivalence (~): nnrat/map-sum-append : map-sum f (append xs ys) ~ map-sum f xs + map-sum f ys The block/partition-decomposition law: the sum over a concatenat |
| [`rainbow.math.rational.nnrat.map-sum-distance`](../src/rainbow/math/rational/nnrat/map_sum_distance.clj) | Distance of finite NNRAT sums is bounded by the sum of distances. |
| [`rainbow.math.rational.nnrat.map-sum-member`](../src/rainbow/math/rational/nnrat/map_sum_member.clj) | A listed nonnegative rational term is bounded by its finite sum. |
| [`rainbow.math.rational.nnrat.map-sum-on`](../src/rainbow/math/rational/nnrat/map_sum_on.clj) | Compatibility entry point for the canonical member-restricted sum theorem. |
| [`rainbow.math.rational.nnrat.map-sum-positive`](../src/rainbow/math/rational/nnrat/map_sum_positive.clj) | Strict positivity of finite exact nonnegative-rational sums. |
| [`rainbow.math.rational.nnrat.map-sum-respects`](../src/rainbow/math/rational/nnrat/map_sum_respects.clj) | map-sum is a congruence for pointwise nnrat equivalence: nnrat/map-sum-respects-equivalence : (forall i, f i ~ g i) -> map-sum f is ~ map-sum g is Lets a per-term equivalence be rewritten underneath a finite sum -- the t |
| [`rainbow.math.rational.nnrat.map-sum-scale`](../src/rainbow/math/rational/nnrat/map_sum_scale.clj) | Scalar pulls through a finite nnrat sum (scalar on the right), up to nnrat equivalence (~): nnrat/map-sum-scale-right : (map-sum f is) * c ~ map-sum (\\i. |
| [`rainbow.math.rational.nnrat.map-sum-zero`](../src/rainbow/math/rational/nnrat/map_sum_zero.clj) | Every term of a vanishing finite nonnegative sum vanishes -- the sum-level form of nonnegativity-forces-zero, stated membership-free by positional split: nnrat/map-sum-zero-at-split : map-sum f (append ps (cons e qs)) ~  |
| [`rainbow.math.rational.nnrat.metric-separation`](../src/rainbow/math/rational/nnrat/metric_separation.clj) | Exact separation for the computational NNRAT distance and finite radius. |
| [`rainbow.math.rational.nnrat.minmax`](../src/rainbow/math/rational/nnrat/minmax.clj) | General exact-rational min/max with UNIVERSAL (forall-quantified) order guarantees. |
| [`rainbow.math.rational.nnrat.monus`](../src/rainbow/math/rational/nnrat/monus.clj) | Layer 2 of the signed->nnrat magnitude foundation: truncated subtraction on Nnrat. |
| [`rainbow.math.rational.nnrat.multiply-commute`](../src/rainbow/math/rational/nnrat/multiply_commute.clj) | Standalone provider of nnrat/multiply-commutative (a*b ~ b*a), extracted so it can be chained WITHOUT nnrat_commutative's bundled nnrat/add-commutative, which alias-conflicts with nnrat_add_monotone's (different proof/sh |
| [`rainbow.math.rational.nnrat.multiply-difference-zero`](../src/rainbow/math/rational/nnrat/multiply_difference_zero.clj) | General nnrat discriminant (both-ordered case): nnrat/multiply-difference-zero-ordered : N1<=P1 -> N2<=P2 -> (P1*P2 + N1*N2 ~ P1*N2 + N1*P2) -> (P1 ~ N1) or (P2 ~ N2). |
| [`rainbow.math.rational.nnrat.multiply-monotone`](../src/rainbow/math/rational/nnrat/multiply_monotone.clj) | Universal monotonicity of nonnegative-rational multiplication under the rational order -- the algebra gap flagged in rainbow-universal-foundation-layer that blocks convex-combination / weighted-average bounds: multiply-m |
| [`rainbow.math.rational.nnrat.multiply-right-monotone`](../src/rainbow/math/rational/nnrat/multiply_right_monotone.clj) | Right-factor monotonicity of nnrat multiplication under the rational order: nnrat/multiply-right-monotone : a <= b -> (a * c) <= (b * c) The mirror of rainbow.math.rational.nnrat.multiply-monotone (left factor). |
| [`rainbow.math.rational.nnrat.multiply-zero-split`](../src/rainbow/math/rational/nnrat/multiply_zero_split.clj) | nnrat/multiply-zero-split : m1*m2 ~ 0 -> (m1 ~ 0) or (m2 ~ 0). |
| [`rainbow.math.rational.nnrat.null-scaling`](../src/rainbow/math/rational/nnrat/null_scaling.clj) | Scaling a null sequence by a bounded constant preserves convergence to zero: analysis/rate-null-scaled : c <= 1 -> rate-null s M -> rate-null (\\n. |
| [`rainbow.math.rational.nnrat.null-sequence`](../src/rainbow/math/rational/nnrat/null_sequence.clj) | Real-analysis toward the OR payoff: null (converging-to-zero) sequences of nonnegative rationals, and the COMPARISON TEST -- a sequence dominated by a null sequence is null. |
| [`rainbow.math.rational.nnrat.order-difference`](../src/rainbow/math/rational/nnrat/order_difference.clj) | Nonnegative-rational order is difference-existence, and the two-point rearrangement inequality that follows from it. |
| [`rainbow.math.rational.nnrat.order-equivalence`](../src/rainbow/math/rational/nnrat/order_equivalence.clj) | Real-analysis roadmap step 2: the nnrat closure<->base order equivalence. |
| [`rainbow.math.rational.nnrat.order-nontrivial`](../src/rainbow/math/rational/nnrat/order_nontrivial.clj) | Constructive impossibility of 1 <= 0 and of k+1 <= k+0 in nnrat order. |
| [`rainbow.math.rational.nnrat.order-scale`](../src/rainbow/math/rational/nnrat/order_scale.clj) | Positive scaling and coefficient normalization for the nnrat order. |
| [`rainbow.math.rational.nnrat.order-total`](../src/rainbow/math/rational/nnrat/order_total.clj) | Totality of the nnrat order: for all a b, a <= b OR b <= a. |
| [`rainbow.math.rational.nnrat.ordered-distance`](../src/rainbow/math/rational/nnrat/ordered_distance.clj) | Exact reconstruction from ordered nonnegative-rational distance. |
| [`rainbow.math.rational.nnrat.positive`](../src/rainbow/math/rational/nnrat/positive.clj) | Constructive strict positivity for exact nonnegative rationals. |
| [`rainbow.math.rational.nnrat.positive-monotone`](../src/rainbow/math/rational/nnrat/positive_monotone.clj) | B6c of the limit-reciprocal arc: positivity of an nnrat is preserved upward under <=. |
| [`rainbow.math.rational.nnrat.positive-succ-form`](../src/rainbow/math/rational/nnrat/positive_succ_form.clj) | A positive nnrat in make(succ p, q) form, so the reciprocal machinery (divide-self-positive / reciprocal-scale-cancel, which are stated for make(succ p, q)) applies to it. |
| [`rainbow.math.rational.nnrat.power`](../src/rainbow/math/rational/nnrat/power.clj) | Exact powers of a nonnegative rational. |
| [`rainbow.math.rational.nnrat.product-reassociation`](../src/rainbow/math/rational/nnrat/product_reassociation.clj) | Associativity and factor reassociation for native nonnegative rationals. |
| [`rainbow.math.rational.nnrat.quadratic-zero`](../src/rainbow/math/rational/nnrat/quadratic_zero.clj) | Zero reflection and the equality case of the nnrat square inequality. |
| [`rainbow.math.rational.nnrat.radius-cancel`](../src/rainbow/math/rational/nnrat/radius_cancel.clj) | The reciprocal radius-cancellation for a general positive nnrat, the linchpin of the limit-product modulus. |
| [`rainbow.math.rational.nnrat.ring`](../src/rainbow/math/rational/nnrat/ring.clj) | A verified nonnegative-rational semiring normalization tactic, up to `nnrat/equivalent`. |
| [`rainbow.math.rational.nnrat.shared-residual-mass`](../src/rainbow/math/rational/nnrat/shared_residual_mass.clj) | Canonical common/residual decomposition, computed without choice. |
| [`rainbow.math.rational.nnrat.square-difference-zero`](../src/rainbow/math/rational/nnrat/square_difference_zero.clj) | The nnrat AM-GM discriminant, ordered case: nnrat/square-difference-zero-ordered : N<=P -> (P*P + N*N ~ P*N + N*P) -> P ~ N. |
| [`rainbow.math.rational.nnrat.square-positive`](../src/rainbow/math/rational/nnrat/square_positive.clj) | nnrat/square-positive : positive k -> positive (k*k). |
| [`rainbow.math.rational.nnrat.square-zero`](../src/rainbow/math/rational/nnrat/square_zero.clj) | nnrat/square-zero : m*m ~ 0 -> m ~ 0. |
| [`rainbow.math.rational.nnrat.strict-order`](../src/rainbow/math/rational/nnrat/strict_order.clj) | Strict order on nonnegative rationals -- the nnrat mirror of signed_strict_order, needed for the no-zero-divisors pair theorem (which case-splits on the nnrat order of a signed value's positive/negative components). |
| [`rainbow.math.rational.nnrat.unit-fraction`](../src/rainbow/math/rational/nnrat/unit_fraction.clj) | Explicit positive unit fractions and their proper complements. |
| [`rainbow.math.rational.nnrat.value-iteration`](../src/rainbow/math/rational/nnrat/value_iteration.clj) | The self-contained value-iteration convergence theorem: a contraction recurrence drives the error to zero. |
| [`rainbow.math.rational.nnrat.weighted-dot`](../src/rainbow/math/rational/nnrat/weighted_dot.clj) | Weighted sum (dot product) of nonnegative-rational coordinate functions over an index list, and its monotonicity in the value coordinates: nnrat/weighted-sum A c x is = sum_i (c i) * (x i) over is : List A nnrat/weighted |
| [`rainbow.math.rational.nnrat.weighted-map-sum-distance`](../src/rainbow/math/rational/nnrat/weighted_map_sum_distance.clj) | Weighted distance lift using the canonical scalar scaling theorem. |
| [`rainbow.math.rational.nnrat.weighted-sum`](../src/rainbow/math/rational/nnrat/weighted_sum.clj) | Universal monotonicity of a two-term nonnegative-rational weighted sum in its values -- the first composite guarantee assembled from the monotonicity foundation (nnrat/multiply-monotone + nnrat/add-monotone): wsum2 w0 w1 |
| [`rainbow.math.rational.nnrat.weighted-sum-bound`](../src/rainbow/math/rational/nnrat/weighted_sum_bound.clj) | Finite-list lift of weighted-term monotonicity. |
| [`rainbow.math.rational.nnrat.weighted-sum-scaled-bound`](../src/rainbow/math/rational/nnrat/weighted_sum_scaled_bound.clj) | Compose the finite weighted-sum bound with right-scaling of a sum. |
| [`rainbow.math.rational.nnrat.weighted-sum-scaling`](../src/rainbow/math/rational/nnrat/weighted_sum_scaling.clj) | Publicly named finite-sum scaling bridge for contraction proofs. |
| [`rainbow.math.rational.nnrat.weighted-term-bound`](../src/rainbow/math/rational/nnrat/weighted_term_bound.clj) | Scalar weighted-term monotonicity for the finite mixture proof. |

## Signed rationals (`src/rainbow/math/rational/signed/`, 136)

| namespace | |
|---|---|
| [`rainbow.math.rational.signed.absolute`](../src/rainbow/math/rational/signed/absolute.clj) | Native absolute value for signed rational proof data. |
| [`rainbow.math.rational.signed.absolute-algebra`](../src/rainbow/math/rational/signed/absolute_algebra.clj) | Quotient-safe algebra for native signed absolute value. |
| [`rainbow.math.rational.signed.absolute-convex`](../src/rainbow/math/rational/signed/absolute_convex.clj) | Absolute value is convex -- the canonical non-smooth convex function, the basis of L1 / robust / minimax objectives. |
| [`rainbow.math.rational.signed.absolute-multiply`](../src/rainbow/math/rational/signed/absolute_multiply.clj) | Brick 3 of limit-product: \|a * b\| ~ \|a\| * \|b\| over signed rationals. |
| [`rainbow.math.rational.signed.absolute-reciprocal`](../src/rainbow/math/rational/signed/absolute_reciprocal.clj) | B5 of the limit-reciprocal arc: the absolute value of a reciprocal, kept through the SAME magnitude(x*x) representative (avoids the absent magnitude-respects / nnrat reciprocal-respects lemmas -- the nnrat-radius-cancel  |
| [`rainbow.math.rational.signed.absolute-reciprocal-times-self`](../src/rainbow/math/rational/signed/absolute_reciprocal_times_self.clj) | B6f prerequisite: the multiplicative absolute reciprocal identity. |
| [`rainbow.math.rational.signed.absolute-sign`](../src/rainbow/math/rational/signed/absolute_sign.clj) | Sign characterization of absolute value over signed rationals: 0 <= w => \|w\| ~ w w <= 0 => \|w\| ~ -w Foundational reusable lemmas (needed by the sign case-splits in limit-product's distance-multiply and absolute-multiply  |
| [`rainbow.math.rational.signed.add-associative`](../src/rainbow/math/rational/signed/add_associative.clj) | Associativity of signed-rational addition up to Grothendieck equivalence. |
| [`rainbow.math.rational.signed.add-zero-reflection`](../src/rainbow/math/rational/signed/add_zero_reflection.clj) | A zero sum of two nonnegative signed rationals has zero summands. |
| [`rainbow.math.rational.signed.additive-distance`](../src/rainbow/math/rational/signed/additive_distance.clj) | Distance bounds from two-sided additive signed inequalities. |
| [`rainbow.math.rational.signed.affine-convex`](../src/rainbow/math/rational/signed/affine_convex.clj) | Affine functions are convex (indeed the convexity inequality is an equality) -- the first substantive instance of signed/convex-on, and the fact that makes linear/affine LP objectives convex (KKT/Lagrangian relevance). |
| [`rainbow.math.rational.signed.big-m`](../src/rainbow/math/rational/signed/big_m.clj) | Soundness of the indicator ("big-M") reformulation. |
| [`rainbow.math.rational.signed.clamp`](../src/rainbow/math/rational/signed/clamp.clj) | Projection of a signed rational into a closed interval. |
| [`rainbow.math.rational.signed.close-of-distance`](../src/rainbow/math/rational/signed/close_of_distance.clj) | B6f lever: build a closeness band from a distance bound (the converse of dist-of-close). |
| [`rainbow.math.rational.signed.close-product`](../src/rainbow/math/rational/signed/close_product.clj) | Brick 4 (band) of limit-product: the product close-band. |
| [`rainbow.math.rational.signed.close-radius-monotone`](../src/rainbow/math/rational/signed/close_radius_monotone.clj) | Band weakening: a closeness band only widens with its radius. |
| [`rainbow.math.rational.signed.constrained-duality`](../src/rainbow/math/rational/signed/constrained_duality.clj) | Lagrangian duality with a CONCRETE penalty: an explicit finite constraint system with explicit multipliers. |
| [`rainbow.math.rational.signed.convergence`](../src/rainbow/math/rational/signed/convergence.clj) | Real-analysis roadmap step 5: the epsilon-N convergence predicate over signed-rational sequences, and the SQUEEZE THEOREM -- the first genuinely-frontier analysis result and the checkpoint that the epsilon-N machinery go |
| [`rainbow.math.rational.signed.convergent-bounded`](../src/rainbow/math/rational/signed/convergent_bounded.clj) | Brick 1 of analysis/limit-product: a convergent sequence is bounded. |
| [`rainbow.math.rational.signed.convergent-bounded-below`](../src/rainbow/math/rational/signed/convergent_bounded_below.clj) | Brick 1 of analysis/limit-reciprocal: a convergent sequence is bounded BELOW near its limit. |
| [`rainbow.math.rational.signed.convex-closure`](../src/rainbow/math/rational/signed/convex_closure.clj) | Closure properties of signed-rational convexity -- the algebra that makes a convex objective composable from convex parts (the convex-optimization bedrock). |
| [`rainbow.math.rational.signed.convex-combination`](../src/rainbow/math/rational/signed/convex_combination.clj) | Two-point convex combination of signed rationals stays within [min, max] -- the signed lift of nnrat/convex-at-most-max / convex-at-least-min, and a foundation brick for convex optimization over signed rationals (connect |
| [`rainbow.math.rational.signed.convex-function`](../src/rainbow/math/rational/signed/convex_function.clj) | The two-point convex-function representation over signed rationals, and its first witnesses -- the base for Jensen's inequality and for connecting convexity to the KKT / Lagrangian optimization lane. |
| [`rainbow.math.rational.signed.convex-optimality`](../src/rainbow/math/rational/signed/convex_optimality.clj) | First-order optimality for convex objectives over signed rationals. |
| [`rainbow.math.rational.signed.decide-completeness`](../src/rainbow/math/rational/signed/decide_completeness.clj) | Completeness of Rainbow's exact-rational decision procedures. |
| [`rainbow.math.rational.signed.decide-equivalence`](../src/rainbow/math/rational/signed/decide_equivalence.clj) | A computable, sound equality test for signed rationals. |
| [`rainbow.math.rational.signed.decide-order`](../src/rainbow/math/rational/signed/decide_order.clj) | A DECIDABLE signed-rational order -- the per-instance half of a certificate. |
| [`rainbow.math.rational.signed.decide-reflexive`](../src/rainbow/math/rational/signed/decide_reflexive.clj) | Decision-level reflexivity for exact rational order. |
| [`rainbow.math.rational.signed.deviation-rows`](../src/rainbow/math/rational/signed/deviation_rows.clj) | The two-row encoding of a magnitude bound says exactly what it looks like. |
| [`rainbow.math.rational.signed.distance`](../src/rainbow/math/rational/signed/distance.clj) | A quotient-safe scalar metric interface for signed rationals. |
| [`rainbow.math.rational.signed.distance-additive`](../src/rainbow/math/rational/signed/distance_additive.clj) | Paired-addition Lipschitz law for quotient-safe signed distance. |
| [`rainbow.math.rational.signed.distance-multiply-absolute`](../src/rainbow/math/rational/signed/distance_multiply_absolute.clj) | Brick 2 of limit-product: distance scales by the ABSOLUTE value of a sign-indefinite left factor. |
| [`rainbow.math.rational.signed.distance-multiply-nonnegative`](../src/rainbow/math/rational/signed/distance_multiply_nonnegative.clj) | Nonnegative signed multiplication bounds quotient-safe distance. |
| [`rainbow.math.rational.signed.distance-negate`](../src/rainbow/math/rational/signed/distance_negate.clj) | d(-a,-b) ~ d(a,b): distance is invariant under negating both points. |
| [`rainbow.math.rational.signed.distance-product`](../src/rainbow/math/rational/signed/distance_product.clj) | Brick 4 (core) of limit-product: the bilinear distance bound for a product. |
| [`rainbow.math.rational.signed.distance-translation`](../src/rainbow/math/rational/signed/distance_translation.clj) | Translation invariance of quotient-safe signed distance. |
| [`rainbow.math.rational.signed.distance-triangle`](../src/rainbow/math/rational/signed/distance_triangle.clj) | Triangle laws for quotient-safe signed absolute value and distance. |
| [`rainbow.math.rational.signed.distributive`](../src/rainbow/math/rational/signed/distributive.clj) | Distributivity of signed multiplication over addition, and the scaled finite sum. |
| [`rainbow.math.rational.signed.dyadic-jensen`](../src/rainbow/math/rational/signed/dyadic_jensen.clj) | Dyadic (four-point) Jensen for signed-rational convex functions -- n-point Jensen for the power-of-two case, reachable WITHOUT the reciprocal wall that blocks general n-point Jensen (which needs weight renormalization by |
| [`rainbow.math.rational.signed.equivalence-laws`](../src/rainbow/math/rational/signed/equivalence_laws.clj) | Symmetry and negation transport for Grothendieck-pair signed equivalence. |
| [`rainbow.math.rational.signed.fubini`](../src/rainbow/math/rational/signed/fubini.clj) | Finite Fubini for signed sums, and the double-counting weak-duality theorem it powers. |
| [`rainbow.math.rational.signed.gap-quality`](../src/rainbow/math/rational/signed/gap_quality.clj) | Universal additive quality from a certified endpoint and reported gap. |
| [`rainbow.math.rational.signed.geometric-bridge`](../src/rainbow/math/rational/signed/geometric_bridge.clj) | Bridge exact NNRAT geometry into signed-rational proof data. |
| [`rainbow.math.rational.signed.half-scale-subtract-self`](../src/rainbow/math/rational/signed/half_scale_subtract_self.clj) | B6e of the limit-reciprocal arc: subtracting half of a value from itself leaves half. |
| [`rainbow.math.rational.signed.indexed-max`](../src/rainbow/math/rational/signed/indexed_max.clj) | Index-aware MAX aggregation -- the argmax semantic core, continuing the non-invasive Level-6 line (indexed-sum -> indexed-max). |
| [`rainbow.math.rational.signed.indexed-max-attains`](../src/rainbow/math/rational/signed/indexed_max_attains.clj) | Attainment for the index-aware max -- the other half of argmax correctness (with dominance). |
| [`rainbow.math.rational.signed.indexed-max-dominates`](../src/rainbow/math/rational/signed/indexed_max_dominates.clj) | Full dominance for the index-aware max: every index below n is bounded by the aggregate. |
| [`rainbow.math.rational.signed.inverse-unique`](../src/rainbow/math/rational/signed/inverse_unique.clj) | B6f lever (replaces the awkward multiply-right-cancel): uniqueness of multiplicative inverse. |
| [`rainbow.math.rational.signed.kkt-sufficiency`](../src/rainbow/math/rational/signed/kkt_sufficiency.clj) | KKT sufficiency: a stationary, feasible, complementary point is a global optimum of a convex program. |
| [`rainbow.math.rational.signed.lagrangian-duality`](../src/rainbow/math/rational/signed/lagrangian_duality.clj) | Lagrangian duality for general constrained optimization over signed rationals. |
| [`rainbow.math.rational.signed.limit-arithmetic`](../src/rainbow/math/rational/signed/limit_arithmetic.clj) | Axiom-free additive arithmetic for signed-rational limits. |
| [`rainbow.math.rational.signed.limit-difference`](../src/rainbow/math/rational/signed/limit_difference.clj) | The difference limit law for signed-rational sequences. |
| [`rainbow.math.rational.signed.limit-negate`](../src/rainbow/math/rational/signed/limit_negate.clj) | Negation preserves signed-rational closeness and limits. |
| [`rainbow.math.rational.signed.limit-order`](../src/rainbow/math/rational/signed/limit_order.clj) | Limits preserve the pointwise order of signed-rational sequences. |
| [`rainbow.math.rational.signed.limit-product`](../src/rainbow/math/rational/signed/limit_product.clj) | The product limit law: the pointwise product of two convergent signed-rational sequences converges to the product of the limits. |
| [`rainbow.math.rational.signed.limit-scalar-laws`](../src/rainbow/math/rational/signed/limit_scalar_laws.clj) | Axiom-free constant and nonnegative-scalar laws for signed order bands. |
| [`rainbow.math.rational.signed.limit-scale`](../src/rainbow/math/rational/signed/limit_scale.clj) | Axiom-free nonnegative scaling of signed-rational order bands. |
| [`rainbow.math.rational.signed.limit-scale-law`](../src/rainbow/math/rational/signed/limit_scale_law.clj) | Scalar multiple of a limit -- the missing piece of limit linearity. |
| [`rainbow.math.rational.signed.limit-square`](../src/rainbow/math/rational/signed/limit_square.clj) | A direct corollary of analysis/limit-product: the square of a convergent signed sequence converges to the square of the limit. |
| [`rainbow.math.rational.signed.limit-uniqueness`](../src/rainbow/math/rational/signed/limit_uniqueness.clj) | Uniqueness of limits for the signed-rational epsilon-N convergence predicate. |
| [`rainbow.math.rational.signed.list-sum`](../src/rainbow/math/rational/signed/list_sum.clj) | Finite sums of signed rationals over a list, and their order laws. |
| [`rainbow.math.rational.signed.lp-capacity-sensitivity`](../src/rainbow/math/rational/signed/lp_capacity_sensitivity.clj) | Capacity sensitivity for signed LP dual bounds. |
| [`rainbow.math.rational.signed.lp-certificate`](../src/rainbow/math/rational/signed/lp_certificate.clj) | A worked LP optimality certificate on concrete numbers, including a NEGATIVE cost -- the per-instance end of the verified-optimization pipeline. |
| [`rainbow.math.rational.signed.lp-certificate-reflect`](../src/rainbow/math/rational/signed/lp_certificate_reflect.clj) | LP optimality certificates by reflection over finite row and column lists. |
| [`rainbow.math.rational.signed.lp-duality`](../src/rainbow/math/rational/signed/lp_duality.clj) | Linear-programming weak duality and the optimality certificate over SIGNED rationals -- arbitrary matrix, costs and right-hand side, any of them negative. |
| [`rainbow.math.rational.signed.lp-duality-on`](../src/rainbow/math/rational/signed/lp_duality_on.clj) | LP weak duality and the optimality certificate, quantified over the rows and columns an instance actually has. |
| [`rainbow.math.rational.signed.lp-equality-row`](../src/rainbow/math/rational/signed/lp_equality_row.clj) | Formal equality-row expansion into two signed inequality rows. |
| [`rainbow.math.rational.signed.lp-equality-row-transport`](../src/rainbow/math/rational/signed/lp_equality_row_transport.clj) | Generic feasibility transport from an original equality to certified actual positive/negative row maps and RHS entries. |
| [`rainbow.math.rational.signed.lp-free-price`](../src/rainbow/math/rational/signed/lp_free_price.clj) | Equality dual-price splitting over signed rationals. |
| [`rainbow.math.rational.signed.lp-objective-negate`](../src/rainbow/math/rational/signed/lp_objective_negate.clj) | Generic finite-sum negation and formal LP minimization sense transport. |
| [`rainbow.math.rational.signed.lp-scaling-bound`](../src/rainbow/math/rational/signed/lp_scaling_bound.clj) | Transport a bound between formal D^2/D-scaled objectives to original sums. |
| [`rainbow.math.rational.signed.lp-scaling-feasibility`](../src/rainbow/math/rational/signed/lp_scaling_feasibility.clj) | Forward feasibility scaling and universal-bound transport on listed indices. |
| [`rainbow.math.rational.signed.magnitude`](../src/rainbow/math/rational/signed/magnitude.clj) | Layer 3 (capstone) of the signed->nnrat magnitude foundation. |
| [`rainbow.math.rational.signed.magnitude-monotone`](../src/rainbow/math/rational/signed/magnitude_monotone.clj) | B6 prerequisite: magnitude is monotone on nonnegatives. |
| [`rainbow.math.rational.signed.map-sum-algebra`](../src/rainbow/math/rational/signed/map_sum_algebra.clj) | Algebra of signed finite sums: congruence, splitting, and the weighted bound. |
| [`rainbow.math.rational.signed.map-sum-scale`](../src/rainbow/math/rational/signed/map_sum_scale.clj) | Nonnegative-rational scaling of signed indexed sums and bilinear objectives. |
| [`rainbow.math.rational.signed.matrix-lp-dimension-decision-duality`](../src/rainbow/math/rational/signed/matrix_lp_dimension_decision_duality.clj) | Signed matrix LP weak duality from executable dimension decisions. |
| [`rainbow.math.rational.signed.matrix-lp-duality`](../src/rainbow/math/rational/signed/matrix_lp_duality.clj) | Signed LP weak duality over native finite matrices and vectors. |
| [`rainbow.math.rational.signed.matrix-lp-row-length-duality`](../src/rainbow/math/rational/signed/matrix_lp_row_length_duality.clj) | Signed matrix LP weak duality from concrete dimension certificates. |
| [`rainbow.math.rational.signed.max-three`](../src/rainbow/math/rational/signed/max_three.clj) | Reusable optimality certificate for a fixed three-candidate maximum. |
| [`rainbow.math.rational.signed.midpoint-convexity`](../src/rainbow/math/rational/signed/midpoint_convexity.clj) | Midpoint convexity over signed rationals: the midpoint stays in [min, max]. |
| [`rainbow.math.rational.signed.minmax`](../src/rainbow/math/rational/signed/minmax.clj) | Universal minimum and maximum over signed rationals. |
| [`rainbow.math.rational.signed.minmax-algebra`](../src/rainbow/math/rational/signed/minmax_algebra.clj) | Algebraic and monotonicity laws for signed extrema. |
| [`rainbow.math.rational.signed.multiply`](../src/rainbow/math/rational/signed/multiply.clj) | Signed-rational multiplication, extending the addition-only signed rationals. |
| [`rainbow.math.rational.signed.multiply-associative`](../src/rainbow/math/rational/signed/multiply_associative.clj) | Associativity of signed multiplication, and the outer swap the LP column bound needs. |
| [`rainbow.math.rational.signed.multiply-monotone`](../src/rainbow/math/rational/signed/multiply_monotone.clj) | Scaling a signed inequality by a nonnegative signed scalar. |
| [`rainbow.math.rational.signed.multiply-nonzero`](../src/rainbow/math/rational/signed/multiply_nonzero.clj) | General signed no-zero-divisors: signed/multiply-zero-split : (a*b ~ 0) -> (a ~ 0) or (b ~ 0) signed/multiply-nonzero : not(a ~ 0) -> not(b ~ 0) -> not(a*b ~ 0). |
| [`rainbow.math.rational.signed.multiply-order`](../src/rainbow/math/rational/signed/multiply_order.clj) | The sign rules for signed-rational multiplication. |
| [`rainbow.math.rational.signed.multiply-positive`](../src/rainbow/math/rational/signed/multiply_positive.clj) | signed/multiply-positive : 0 < a -> 0 < b -> 0 < a*b. |
| [`rainbow.math.rational.signed.multiply-ring`](../src/rainbow/math/rational/signed/multiply_ring.clj) | Signed multiplication is commutative and well defined on the Grothendieck quotient. |
| [`rainbow.math.rational.signed.negate-additive`](../src/rainbow/math/rational/signed/negate_additive.clj) | Signed negation distributes over addition up to signed equivalence. |
| [`rainbow.math.rational.signed.no-zero-divisors`](../src/rainbow/math/rational/signed/no_zero_divisors.clj) | No-zero-divisors sub-foundation for strict convexity: nonzero facts and (building up) a != 0 -> b != 0 -> a*b != 0. |
| [`rainbow.math.rational.signed.one-hot-attained`](../src/rainbow/math/rational/signed/one_hot_attained.clj) | THE ONE-HOT SELECTOR / ATTAINMENT LEMMA, the shared Level-3 reading of every checker that certifies a minimum or maximum with a 0/1 witness (the max/min-type checks). |
| [`rainbow.math.rational.signed.one-hot-keep`](../src/rainbow/math/rational/signed/one_hot_keep.clj) | THE ONE-HOT ATTAINMENT LEMMA WITH A KEEP OPTION, in the sign convention the relaxation checkers use (Bellman-Ford round, Dijkstra step, Floyd-Warshall round). |
| [`rainbow.math.rational.signed.one-hot-selects`](../src/rainbow/math/rational/signed/one_hot_selects.clj) | THE ONE-HOT VALUE SELECTOR, the shared Level-3 reading of every checker that pins a value to a one-hot sum: Floyd-Warshall's pivot column and row, Dijkstra's chosen label and row, and the rest. |
| [`rainbow.math.rational.signed.one-hot-unique`](../src/rainbow/math/rational/signed/one_hot_unique.clj) | A ONE-HOT SELECTOR SELECTS ONE INDEX. |
| [`rainbow.math.rational.signed.order`](../src/rainbow/math/rational/signed/order.clj) | Order and structural laws for signed rationals. |
| [`rainbow.math.rational.signed.order-cancellation`](../src/rainbow/math/rational/signed/order_cancellation.clj) | Additive cancellation for signed-rational order. |
| [`rainbow.math.rational.signed.order-monotone`](../src/rainbow/math/rational/signed/order_monotone.clj) | Real-analysis roadmap step 6a: signed order is monotone under addition -- signed/add-right-monotone : a <= b -> (a + c) <= (b + c) signed/add adds pos/neg componentwise (pos(a+c) = pos a + pos c, etc. |
| [`rainbow.math.rational.signed.order-respects`](../src/rainbow/math/rational/signed/order_respects.clj) | Equivalence transport for signed order and signed-sequence convergence. |
| [`rainbow.math.rational.signed.order-transitivity`](../src/rainbow/math/rational/signed/order_transitivity.clj) | Real-analysis roadmap step 4: transitivity of the signed-rational order. |
| [`rainbow.math.rational.signed.pointwise-order`](../src/rainbow/math/rational/signed/pointwise_order.clj) | Pointwise order over the indices a problem actually has. |
| [`rainbow.math.rational.signed.product-radius-nonneg`](../src/rainbow/math/rational/signed/product_radius_nonneg.clj) | First sub-proof of the limit-product modulus assembly: the radius base V = (1 + \|L\|) + \|M\| is nonnegative (indeed a sum of nonnegatives), so signed/from-nnrat-magnitude applies to it. |
| [`rainbow.math.rational.signed.product-radius-positive`](../src/rainbow/math/rational/signed/product_radius_positive.clj) | Second sub-proof of the limit-product modulus assembly: the magnitude of the radius base V = (1+\|L\|)+\|M\| has a positive numerator, so nnrat/make-succ-of-positive-numerator and analysis/nnrat-radius-cancel apply to it. |
| [`rainbow.math.rational.signed.rate-order`](../src/rainbow/math/rational/signed/rate_order.clj) | Order closure under vanishing signed-rational error bounds. |
| [`rainbow.math.rational.signed.rational`](../src/rainbow/math/rational/signed/rational.clj) | Signed rationals as proof data: a pair (positive, negative) of nonnegative rationals denoting positive - negative. |
| [`rainbow.math.rational.signed.reciprocal`](../src/rainbow/math/rational/signed/reciprocal.clj) | The signed-rational reciprocal operation and its self-inverse law -- the missing field operation. |
| [`rainbow.math.rational.signed.reciprocal-absolute-bound`](../src/rainbow/math/rational/signed/reciprocal_absolute_bound.clj) | Layer A of the limit-reciprocal assembly: bound the absolute reciprocal of x by the reciprocal of a positive lower bound on \|x\|. |
| [`rainbow.math.rational.signed.reciprocal-antitone`](../src/rainbow/math/rational/signed/reciprocal_antitone.clj) | B4 of the limit-reciprocal arc: reciprocal reverses order on positives, plus the two reusable order<->subtract-nonneg bridges it needs. |
| [`rainbow.math.rational.signed.reciprocal-difference`](../src/rainbow/math/rational/signed/reciprocal_difference.clj) | The reciprocal-difference identity: the algebraic heart of the limit-reciprocal law. |
| [`rainbow.math.rational.signed.reciprocal-nonnegative`](../src/rainbow/math/rational/signed/reciprocal_nonnegative.clj) | B3 of the limit-reciprocal arc: the reciprocal of a nonnegative signed rational is nonnegative. |
| [`rainbow.math.rational.signed.recovery-laws`](../src/rainbow/math/rational/signed/recovery_laws.clj) | Two general signed-rational laws that the corpus lacked, proved en route to the Gauss-Seidel exactness theorem and promoted here so any module can reuse them without depending on an application module. |
| [`rainbow.math.rational.signed.scale-additive`](../src/rainbow/math/rational/signed/scale_additive.clj) | Nonnegative-rational scaling distributes over signed addition up to Grothendieck equivalence. |
| [`rainbow.math.rational.signed.scale-composition`](../src/rainbow/math/rational/signed/scale_composition.clj) | Composition of nonnegative scaling on signed rationals. |
| [`rainbow.math.rational.signed.scale-order`](../src/rainbow/math/rational/signed/scale_order.clj) | Nonnegative-rational scaling preserves signed order. |
| [`rainbow.math.rational.signed.scale-reflection`](../src/rainbow/math/rational/signed/scale_reflection.clj) | Positive rational scaling reflects signed order. |
| [`rainbow.math.rational.signed.square-convex`](../src/rainbow/math/rational/signed/square_convex.clj) | Square convexity over signed rationals -- the canonical non-trivial convex function. |
| [`rainbow.math.rational.signed.square-minimizer-unique`](../src/rainbow/math/rational/signed/square_minimizer_unique.clj) | Concrete OR-Commons decision object: the square objective (\\x. |
| [`rainbow.math.rational.signed.square-monotone`](../src/rainbow/math/rational/signed/square_monotone.clj) | B6b of the limit-reciprocal arc: squaring is monotone on nonnegatives. |
| [`rainbow.math.rational.signed.square-nonzero`](../src/rainbow/math/rational/signed/square_nonzero.clj) | signed/square-nonzero : not(d ~ 0) -> not(d*d ~ 0). |
| [`rainbow.math.rational.signed.square-numerator-positive`](../src/rainbow/math/rational/signed/square_numerator_positive.clj) | B6d of the limit-reciprocal arc: the positivity derivation the assembly calls. |
| [`rainbow.math.rational.signed.square-numerator-positive-of-absolute`](../src/rainbow/math/rational/signed/square_numerator_positive_of_absolute.clj) | B6f prerequisite (s-n positivity transfer): a lower bound on \|x\| makes x*x have positive magnitude-numerator. |
| [`rainbow.math.rational.signed.square-of-sum`](../src/rainbow/math/rational/signed/square_of_sum.clj) | The four-term expansion of a squared sum over signed rationals -- a reusable step for square convexity (the variance inequality) and other quadratic identities. |
| [`rainbow.math.rational.signed.square-strict-convex`](../src/rainbow/math/rational/signed/square_strict_convex.clj) | Strict convexity of the square, the capstone of the no-zero-divisors work: signed/strict-convex-on f := forall w0 w1 x y, 0<w0 -> 0<w1 -> (w0+w1 ~ 1) -> x !~ y -> f(wsum) < wsum(f x, f y) signed/square-strict-convex : st |
| [`rainbow.math.rational.signed.square-zero`](../src/rainbow/math/rational/signed/square_zero.clj) | A signed rational whose square is zero is itself zero. |
| [`rainbow.math.rational.signed.stl`](../src/rainbow/math/rational/signed/stl.clj) | Signed minimum and maximum for signal temporal logic (STL) robustness. |
| [`rainbow.math.rational.signed.strict-convex-unique`](../src/rainbow/math/rational/signed/strict_convex_unique.clj) | Uniqueness of the minimizer for a strictly convex function -- the OR-Commons payoff of the convexity lane: a strictly convex objective has at most one minimizer (up to equivalence). |
| [`rainbow.math.rational.signed.strict-order`](../src/rainbow/math/rational/signed/strict_order.clj) | Strict order on signed rationals -- the foundation strict convexity (and unique-minimizer results) need, which the non-strict `signed/at-most` lane lacked. |
| [`rainbow.math.rational.signed.structural-equality`](../src/rainbow/math/rational/signed/structural_equality.clj) | Decidable STRUCTURAL equality for nonnegative and signed rationals. |
| [`rainbow.math.rational.signed.unit-laws`](../src/rainbow/math/rational/signed/unit_laws.clj) | The unit and self-cancellation laws the signed layer was missing. |
| [`rainbow.math.rational.signed.upper-bound-program`](../src/rainbow/math/rational/signed/upper_bound_program.clj) | A worked constrained program, certified end-to-end by the general duality theorem -- the non-vacuity witness for the signed Lagrangian stack. |
| [`rainbow.math.rational.signed.vector-sup-congruence`](../src/rainbow/math/rational/signed/vector_sup_congruence.clj) | Quotient-safe congruence of signed-list sup distance. |
| [`rainbow.math.rational.signed.vector-sup-distance`](../src/rainbow/math/rational/signed/vector_sup_distance.clj) | Finite maxima and sup distance for signed-rational list vectors. |
| [`rainbow.math.rational.signed.vector-sup-separation`](../src/rainbow/math/rational/signed/vector_sup_separation.clj) | Zero separation for signed-list sup distance at fixed shape. |
| [`rainbow.math.rational.signed.vector-sup-translation`](../src/rainbow/math/rational/signed/vector_sup_translation.clj) | Fixed-shape translation invariance of signed-list sup distance. |
| [`rainbow.math.rational.signed.vector-sup-triangle`](../src/rainbow/math/rational/signed/vector_sup_triangle.clj) | Triangle inequality for equal-shaped signed-rational list vectors. |

## Sets (`src/rainbow/math/sets/`, 16)

| namespace | |
|---|---|
| [`rainbow.math.sets.fiber-characterization`](../src/rainbow/math/sets/fiber_characterization.clj) | Image, surjection, and injection characterized by their source fibers. |
| [`rainbow.math.sets.fiber-unique`](../src/rainbow/math/sets/fiber_unique.clj) | Unique existence from subsingleton predicates, applied to bijection fibers. |
| [`rainbow.math.sets.image-certificates`](../src/rainbow/math/sets/image_certificates.clj) | Constructive image/target inclusions from certified set maps. |
| [`rainbow.math.sets.image-composition`](../src/rainbow/math/sets/image_composition.clj) | The image of a composite map is the nested image, by mutual inclusion. |
| [`rainbow.math.sets.image-difference`](../src/rainbow/math/sets/image_difference.clj) | Images preserve set difference exactly when witnesses cannot collide. |
| [`rainbow.math.sets.image-insert`](../src/rainbow/math/sets/image_insert.clj) | Images commute constructively with inserting one source value. |
| [`rainbow.math.sets.image-lattice`](../src/rainbow/math/sets/image_lattice.clj) | Images preserve unions, and preserve intersections under injectivity. |
| [`rainbow.math.sets.image-preimage-adjunction`](../src/rainbow/math/sets/image_preimage_adjunction.clj) | The constructive image/preimage Galois connection for set inclusion. |
| [`rainbow.math.sets.inverse-certificates`](../src/rainbow/math/sets/inverse_certificates.clj) | Constructive injectivity, surjectivity, and bijectivity from set inverses. |
| [`rainbow.math.sets.inverse-unique-fiber`](../src/rainbow/math/sets/inverse_unique_fiber.clj) | Two-sided set inverses provide unique witnesses in every target fiber. |
| [`rainbow.math.sets.map-composition`](../src/rainbow/math/sets/map_composition.clj) | Constructive set-map properties preserved by function composition. |
| [`rainbow.math.sets.preimage-composition`](../src/rainbow/math/sets/preimage_composition.clj) | Identity and composition laws for set preimages. |
| [`rainbow.math.sets.preimage-lattice`](../src/rainbow/math/sets/preimage_lattice.clj) | Preimages preserve intersection, union, and difference by exact reuse. |
| [`rainbow.math.sets.range`](../src/rainbow/math/sets/range.clj) | Lean-compatible Set range ordering and native finite-range laws. |
| [`rainbow.math.sets.range-image-bridge`](../src/rainbow/math/sets/range_image_bridge.clj) | Bridge global function ranges to images of universal source sets. |
| [`rainbow.math.sets.range-surjective`](../src/rainbow/math/sets/range_surjective.clj) | Characterize surjections by their universal ranges. |

## Finite sets (`src/rainbow/math/sets/finset/`, 5)

| namespace | |
|---|---|
| [`rainbow.math.sets.finset.data`](../src/rainbow/math/sets/finset/data.clj) | Computational finite sets: duplicate-free enumerations paired with proof data. |
| [`rainbow.math.sets.finset.filter`](../src/rainbow/math/sets/finset/filter.clj) | Certified predicates and extensional filtering for native Finsets. |
| [`rainbow.math.sets.finset.nontrivial`](../src/rainbow/math/sets/finset/nontrivial.clj) | Nontrivial native Finsets through their extensional predicate view. |
| [`rainbow.math.sets.finset.powerset`](../src/rainbow/math/sets/finset/powerset.clj) | Finite-set powersets derived from extensional Set and Finset proof data. |
| [`rainbow.math.sets.finset.range`](../src/rainbow/math/sets/finset/range.clj) | Native initial segments of Nat and finite-Finset range bounds. |

## Finite sums (`src/rainbow/math/sums/`, 37)

| namespace | |
|---|---|
| [`rainbow.math.sums.admissions-block`](../src/rainbow/math/sums/admissions_block.clj) | A blocking indicator vanishes exactly when the student does not improve, or the college has neither vacancy nor rank improvement. |
| [`rainbow.math.sums.binary-capacity`](../src/rainbow/math/sums/binary_capacity.clj) | For binary entries, x+y<=1 means selecting x excludes y. |
| [`rainbow.math.sums.binary-conflicts`](../src/rainbow/math/sums/binary_conflicts.clj) | Reusable bridges from binary entries and nonpositive nonnegative sums to exclusions. |
| [`rainbow.math.sums.binary-mutuality`](../src/rainbow/math/sums/binary_mutuality.clj) | Mutual selected-edge implications identify binary entries. |
| [`rainbow.math.sums.boolean-predicate`](../src/rainbow/math/sums/boolean_predicate.clj) | The converse of the existing zero/one polynomial lemma, for predicate adapters. |
| [`rainbow.math.sums.bpath-cut`](../src/rainbow/math/sums/bpath_cut.clj) | Cut/exit proof support for bottleneck paths. |
| [`rainbow.math.sums.bpath-walk`](../src/rainbow/math/sums/bpath_walk.clj) | Finite one-hot walks crossing a binary cut. |
| [`rainbow.math.sums.budgeted-protection`](../src/rainbow/math/sums/budgeted_protection.clj) | Weak duality for a budgeted box: 0<=w<=1, sum w<=Gamma and d_j<=z+p_j, z,p>=0 imply sum w_j*d_j<=Gamma*z+sum p_j. |
| [`rainbow.math.sums.earliest-schedule`](../src/rainbow/math/sums/earliest_schedule.clj) | The earliest-start recurrence preserves feasibility whenever any window schedule exists. |
| [`rainbow.math.sums.equality-lp-bound`](../src/rainbow/math/sums/equality_lp_bound.clj) | Weak duality for equality rows and unrestricted dual prices. |
| [`rainbow.math.sums.flow-cut`](../src/rainbow/math/sums/flow_cut.clj) | General lemmas: flow cut. |
| [`rainbow.math.sums.indicator-zero`](../src/rainbow/math/sums/indicator_zero.clj) | A zero sum of strict-violation indicators means every weak inequality holds. |
| [`rainbow.math.sums.lp-bounds`](../src/rainbow/math/sums/lp_bounds.clj) | Finite covering duality and certificate-gap arithmetic, reusing the existing list-backed LP theorem. |
| [`rainbow.math.sums.lp-mixed-bound`](../src/rainbow/math/sums/lp_mixed_bound.clj) | A free-price equality block, nonnegative-price upper rows and unit upper bounds. |
| [`rainbow.math.sums.lp-two-blocks`](../src/rainbow/math/sums/lp_two_blocks.clj) | Weak duality with two separate constraint blocks, by two applications of the existing LP theorem. |
| [`rainbow.math.sums.nonblocking`](../src/rainbow/math/sums/nonblocking.clj) | An encoded maximum is nonnegative exactly when at least one preference gap is. |
| [`rainbow.math.sums.nonneg-zero`](../src/rainbow/math/sums/nonneg_zero.clj) | Nonnegative terms that sum to zero are each zero, over signed/expr-sum-value: if 0 <= F i for every i < k and sum F k ~ 0 then F i ~ 0 for every i < k. |
| [`rainbow.math.sums.of-nat`](../src/rainbow/math/sums/of_nat.clj) | The bridge between a natural-number count written as the signed literal of-nat n = n/1 (the form the checkers use, e.g. |
| [`rainbow.math.sums.one-hot-factor`](../src/rainbow/math/sums/one_hot_factor.clj) | Reusable selection factorization for arbitrary signed values. |
| [`rainbow.math.sums.one-hot-index`](../src/rainbow/math/sums/one_hot_index.clj) | Every selected index reads every one-hot weighted sum; every distinct index is zero. |
| [`rainbow.math.sums.one-hot-pair`](../src/rainbow/math/sums/one_hot_pair.clj) | Two independent one-hot rows select exactly the corresponding matrix entry. |
| [`rainbow.math.sums.one-hot-value`](../src/rainbow/math/sums/one_hot_value.clj) | Pointwise values of a selected index, their weighted equality, and explicit attainment. |
| [`rainbow.math.sums.pareto-mask`](../src/rainbow/math/sums/pareto_mask.clj) | The Pareto penalty mask is equivalent to absence of strict gain under componentwise dominance. |
| [`rainbow.math.sums.period-usage`](../src/rainbow/math/sums/period_usage.clj) | Multiplying two Boolean indicators by a weight equals filtering that weight by both tests. |
| [`rainbow.math.sums.permutation-invariant`](../src/rainbow/math/sums/permutation_invariant.clj) | Nonlinear two-coordinate sums are invariant under a binary permutation matrix. |
| [`rainbow.math.sums.predicate-bridges`](../src/rainbow/math/sums/predicate_bridges.clj) | Reusable bridges from checker indicators and squared norms to mathematical predicates. |
| [`rainbow.math.sums.selected-minimum`](../src/rainbow/math/sums/selected_minimum.clj) | A one-hot selected minimum among non-excluded entries. |
| [`rainbow.math.sums.single-support`](../src/rainbow/math/sums/single_support.clj) | Single supported terms and tight finite unit-capacity sums. |
| [`rainbow.math.sums.strict-indicator`](../src/rainbow/math/sums/strict_indicator.clj) | A strict comparison indicator is one exactly when the reverse weak inequality is false. |
| [`rainbow.math.sums.triangular`](../src/rainbow/math/sums/triangular.clj) | Triangular decomposition for the existing finite sums; prefix completion costs. |
| [`rainbow.math.sums.two-terms`](../src/rainbow/math/sums/two_terms.clj) | One term, and two DISTINCT terms, are bounded by a nonnegative expr-sum-value. |
| [`rainbow.math.sums.value-algebra`](../src/rainbow/math/sums/value_algebra.clj) | Finite-sum algebra for the existing signed/expr-sum-value. |
| [`rainbow.math.sums.value-append`](../src/rainbow/math/sums/value_append.clj) | Split the existing expr-sum-value at any Nat offset a: sum F (b+a) ~ sum F a + sum (fn i. |
| [`rainbow.math.sums.wspt-order`](../src/rainbow/math/sums/wspt_order.clj) | WSPT order prerequisites. |
| [`rainbow.math.sums.wspt-pair-bound`](../src/rainbow/math/sums/wspt_pair_bound.clj) | Pairwise lower bound for a prefix completion objective, exact for sorted pairs. |
| [`rainbow.math.sums.wspt-permutation`](../src/rainbow/math/sums/wspt_permutation.clj) | WSPT optimality over all permutation matrices, with positive processing times. |
| [`rainbow.math.sums.zero-violations`](../src/rainbow/math/sums/zero_violations.clj) | Zero positive-part penalties mean no violated inequality; a minimum encodes disjunction. |

## Algorithm guarantees (`src/rainbow/algorithms/proofs/`, 85)

| namespace | |
|---|---|
| [`rainbow.algorithms.proofs.adadelta`](../src/rainbow/algorithms/proofs/adadelta.clj) | AHoF O23 Adadelta: the learning-rate-free update scale. |
| [`rainbow.algorithms.proofs.adam`](../src/rainbow/algorithms/proofs/adam.clj) | AHoF O24 Adam: the first-moment (momentum) estimate and the preconditioned step direction. |
| [`rainbow.algorithms.proofs.adaptive-gradient`](../src/rainbow/algorithms/proofs/adaptive_gradient.clj) | AHoF O21 AdaGrad: the adaptive per-parameter learning rate. |
| [`rainbow.algorithms.proofs.admm`](../src/rainbow/algorithms/proofs/admm.clj) | AHoF O51 ADMM (Alternating Direction Method of Multipliers): the scaled-form dual variable update over vector-valued state. |
| [`rainbow.algorithms.proofs.argmax-index`](../src/rainbow/algorithms/proofs/argmax_index.clj) | Argmax over a list of nonnegative rationals, returning the INDEX of the maximum element (the first index attaining it): argmax-index [x0, x1, ...] = the i minimizing (-x_i), ties to the earliest. |
| [`rainbow.algorithms.proofs.augmented-lagrangian`](../src/rainbow/algorithms/proofs/augmented_lagrangian.clj) | AHoF O49 Augmented Lagrangian: the dual multiplier update in the outer loop. |
| [`rainbow.algorithms.proofs.bayesian-learning`](../src/rainbow/algorithms/proofs/bayesian_learning.clj) | Bayesian parameter learning over exact rationals. |
| [`rainbow.algorithms.proofs.bellman-contraction`](../src/rainbow/algorithms/proofs/bellman_contraction.clj) | Finite fixed-policy Bellman contraction over exact natural numerators. |
| [`rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness`](../src/rainbow/algorithms/proofs/bellman_scaled_fixed_point_uniqueness.clj) | Constructive uniqueness of scaled fixed points for finite Bellman numerators. |
| [`rainbow.algorithms.proofs.bisection`](../src/rainbow/algorithms/proofs/bisection.clj) | Bisection bracket search over exact nonnegative rationals. |
| [`rainbow.algorithms.proofs.box-projection`](../src/rainbow/algorithms/proofs/box_projection.clj) | AHoF box projection (the projection step of Projected Gradient Descent and box-constrained optimization): after an unconstrained gradient step lands at x, the iterate is projected back onto the feasible box [lo, hi] by c |
| [`rainbow.algorithms.proofs.branch-and-bound`](../src/rainbow/algorithms/proofs/branch_and_bound.clj) | AHoF D34 / O-family Branch and Bound: the bounding test that turns exhaustive enumeration into a pruned search. |
| [`rainbow.algorithms.proofs.composite-metric`](../src/rainbow/algorithms/proofs/composite_metric.clj) | Composite evaluation metrics over exact rationals. |
| [`rainbow.algorithms.proofs.conjugate-gradient`](../src/rainbow/algorithms/proofs/conjugate_gradient.clj) | Conjugate gradient descent over signed rationals with pair-valued state. |
| [`rainbow.algorithms.proofs.coordinate-search`](../src/rainbow/algorithms/proofs/coordinate_search.clj) | Cyclic coordinate search over signed-rational pair state. |
| [`rainbow.algorithms.proofs.counterfactual`](../src/rainbow/algorithms/proofs/counterfactual.clj) | AHoF V57 Counterfactual Explanation: the proximity term of the counterfactual search objective. |
| [`rainbow.algorithms.proofs.counterfactual-distance-laws`](../src/rainbow/algorithms/proofs/counterfactual_distance_laws.clj) | Native algebraic laws for exact counterfactual squared distance. |
| [`rainbow.algorithms.proofs.counterfactual-distance-separation`](../src/rainbow/algorithms/proofs/counterfactual_distance_separation.clj) | Native separation laws for the existing counterfactual squared distance. |
| [`rainbow.algorithms.proofs.counterfactual-objective-laws`](../src/rainbow/algorithms/proofs/counterfactual_objective_laws.clj) | Native guarantees for the exact counterfactual optimization objective. |
| [`rainbow.algorithms.proofs.cross-validation`](../src/rainbow/algorithms/proofs/cross_validation.clj) | K-fold cross-validation mean over exact rationals. |
| [`rainbow.algorithms.proofs.cuckoo-search`](../src/rainbow/algorithms/proofs/cuckoo_search.clj) | AHoF O47 Cuckoo Search: the Levy-flight step over vector-valued state. |
| [`rainbow.algorithms.proofs.decision-guarantee-audit`](../src/rainbow/algorithms/proofs/decision_guarantee_audit.clj) | Finite exact-rational decision-bound auditing as native proof data. |
| [`rainbow.algorithms.proofs.decision-network`](../src/rainbow/algorithms/proofs/decision_network.clj) | Decision network evaluation over exact rationals. |
| [`rainbow.algorithms.proofs.differential-evolution`](../src/rainbow/algorithms/proofs/differential_evolution.clj) | AHoF O44 Differential Evolution: the differential mutation over vector-valued population members. |
| [`rainbow.algorithms.proofs.dual-ascent`](../src/rainbow/algorithms/proofs/dual_ascent.clj) | AHoF O52 Dual Ascent: the dual-variable ascent step over vector-valued multipliers. |
| [`rainbow.algorithms.proofs.edit-distance`](../src/rainbow/algorithms/proofs/edit_distance.clj) | AHoF edit distance / Levenshtein alignment DP cell. |
| [`rainbow.algorithms.proofs.eligibility-traces`](../src/rainbow/algorithms/proofs/eligibility_traces.clj) | Eligibility traces (TD(lambda)) over exact rationals. |
| [`rainbow.algorithms.proofs.exact-inference`](../src/rainbow/algorithms/proofs/exact_inference.clj) | Exact Bayesian inference by enumeration over a finite hidden variable. |
| [`rainbow.algorithms.proofs.factorial`](../src/rainbow/algorithms/proofs/factorial.clj) | AHoF factorial n! |
| [`rainbow.algorithms.proofs.failure-probability-monitor`](../src/rainbow/algorithms/proofs/failure_probability_monitor.clj) | Runtime failure-probability monitoring over exact rationals (AHoF V64). |
| [`rainbow.algorithms.proofs.feature-importance`](../src/rainbow/algorithms/proofs/feature_importance.clj) | AHoF V54 Permutation Feature Importance: the drop in model score when a feature's values are permuted, measuring how much the model relies on it: importance(feature) = baseline-score - permuted-score a signed subtraction |
| [`rainbow.algorithms.proofs.fibonacci`](../src/rainbow/algorithms/proofs/fibonacci.clj) | AHoF Fibonacci numbers -- the linear recurrence behind Fibonacci search (the derivative-free line-search that places probes at Fibonacci ratios) and a canonical dynamic-programming example. |
| [`rainbow.algorithms.proofs.firefly`](../src/rainbow/algorithms/proofs/firefly.clj) | AHoF O46 Firefly Algorithm: the attraction move over vector-valued state. |
| [`rainbow.algorithms.proofs.floyd-warshall`](../src/rainbow/algorithms/proofs/floyd_warshall.clj) | AHoF Floyd-Warshall all-pairs shortest paths -- the dynamic-programming relaxation through an intermediate node. |
| [`rainbow.algorithms.proofs.full-factorial`](../src/rainbow/algorithms/proofs/full_factorial.clj) | AHoF O58 Full Factorial Sampling: the design size is the product of the per-dimension level counts. |
| [`rainbow.algorithms.proofs.general-descent`](../src/rainbow/algorithms/proofs/general_descent.clj) | The general descent skeleton over signed rationals: the parent of the whole descent family. |
| [`rainbow.algorithms.proofs.golden-section-search`](../src/rainbow/algorithms/proofs/golden_section_search.clj) | Golden Section Search interval reduction over exact rationals (AHoF O9). |
| [`rainbow.algorithms.proofs.gradient-ascent`](../src/rainbow/algorithms/proofs/gradient_ascent.clj) | Bounded fixed-rate gradient ascent over exact nonnegative rationals. |
| [`rainbow.algorithms.proofs.gradient-descent`](../src/rainbow/algorithms/proofs/gradient_descent.clj) | Bounded fixed-rate gradient descent over signed rationals. |
| [`rainbow.algorithms.proofs.histogram-bin`](../src/rainbow/algorithms/proofs/histogram_bin.clj) | AHoF histogram / kernel-density bin count: the number of sample values that fall inside a half-open-style bin [lo, hi], count-in-range lo hi xs = \|{ x in xs : lo <= x and x <= hi }\|, the primitive behind histograms and ( |
| [`rainbow.algorithms.proofs.hooke-jeeves`](../src/rainbow/algorithms/proofs/hooke_jeeves.clj) | AHoF O34 Hooke-Jeeves pattern search: the exploratory probe and the pattern (acceleration) move over vector-valued state. |
| [`rainbow.algorithms.proofs.hypergradient`](../src/rainbow/algorithms/proofs/hypergradient.clj) | AHoF O25 Hypergradient Descent: the meta-optimizer that tunes its own learning rate by the gradient of the loss with respect to the learning rate. |
| [`rainbow.algorithms.proofs.importance-sampling`](../src/rainbow/algorithms/proofs/importance_sampling.clj) | Likelihood-weighted (importance) sampling estimates over exact rationals. |
| [`rainbow.algorithms.proofs.inner-product`](../src/rainbow/algorithms/proofs/inner_product.clj) | The vector dot product (inner product) over signed-rational vectors: dot [a1..an] [b1..bn] = sum_i a_i * b_i This is a zip of the two component lists with signed multiplication, summed with signed addition -- a nested `d |
| [`rainbow.algorithms.proofs.interior-point`](../src/rainbow/algorithms/proofs/interior_point.clj) | AHoF O50 Interior Point / Barrier Method: the transform that keeps iterates strictly feasible by adding a barrier term that grows as a constraint slack approaches zero: barrier-objective = objective + mu * (1 / slack) wh |
| [`rainbow.algorithms.proofs.interval-arithmetic`](../src/rainbow/algorithms/proofs/interval_arithmetic.clj) | AHoF V40 Interval Arithmetic: the sound enclosure of a signed-rational value by a lower/upper bound pair, with the additive interval operation that underlies the reachability propagators (V40-V47). |
| [`rainbow.algorithms.proofs.interval-membership`](../src/rainbow/algorithms/proofs/interval_membership.clj) | Interval membership over exact rationals (AHoF V40, decision layer). |
| [`rainbow.algorithms.proofs.latin-hypercube`](../src/rainbow/algorithms/proofs/latin_hypercube.clj) | AHoF O59 Latin Hypercube Sampling: a space-filling design that draws exactly n sample points across any number k of dimensions, in contrast to the full factorial design (O58) whose size grows as the product of per-dimens |
| [`rainbow.algorithms.proofs.levenberg-marquardt`](../src/rainbow/algorithms/proofs/levenberg_marquardt.clj) | Levenberg-Marquardt as the general descent skeleton with a damped Hessian-inverse step size. |
| [`rainbow.algorithms.proofs.list-maximum`](../src/rainbow/algorithms/proofs/list_maximum.clj) | Maximum of a list of nonnegative rationals, as a native fold: list-maximum [x0, x1, ...] = max(x0, max(x1, ... |
| [`rainbow.algorithms.proofs.list-product`](../src/rainbow/algorithms/proofs/list_product.clj) | Product of a list of nonnegative rationals, as a native fold: list-product [x0, x1, ...] = x0 * x1 * ... |
| [`rainbow.algorithms.proofs.local-search`](../src/rainbow/algorithms/proofs/local_search.clj) | Bounded local (hill-climbing) search over a finite candidate set with exact rational objectives. |
| [`rainbow.algorithms.proofs.maximum-likelihood`](../src/rainbow/algorithms/proofs/maximum_likelihood.clj) | Maximum likelihood estimation over exact rationals. |
| [`rainbow.algorithms.proofs.metropolis`](../src/rainbow/algorithms/proofs/metropolis.clj) | AHoF V22 Metropolis-Hastings acceptance (also the acceptance rule of Simulated Annealing): a proposed state is scored by an energy (cost), and the Metropolis rule always accepts a downhill proposal, while an uphill propo |
| [`rainbow.algorithms.proofs.minimax`](../src/rainbow/algorithms/proofs/minimax.clj) | AHoF adversarial decision-making -- the minimax value of a two-ply zero-sum game. |
| [`rainbow.algorithms.proofs.momentum`](../src/rainbow/algorithms/proofs/momentum.clj) | Polyak momentum descent over signed rationals with pair-valued state. |
| [`rainbow.algorithms.proofs.nearest-neighbor`](../src/rainbow/algorithms/proofs/nearest_neighbor.clj) | Nearest-neighbor value function approximation over exact rationals. |
| [`rainbow.algorithms.proofs.nelder-mead`](../src/rainbow/algorithms/proofs/nelder_mead.clj) | AHoF O36 Nelder-Mead Simplex: the reflection move, the workhorse simplex transform. |
| [`rainbow.algorithms.proofs.nesterov`](../src/rainbow/algorithms/proofs/nesterov.clj) | Nesterov accelerated momentum over signed rationals with pair-valued state. |
| [`rainbow.algorithms.proofs.net-flow`](../src/rainbow/algorithms/proofs/net_flow.clj) | AHoF net flow / net present value: the signed balance of inflows against outflows, net inflow outflow = inflow - outflow, the exact-rational primitive behind net-reward MDPs, cash-flow / NPV accounting, and constraint re |
| [`rainbow.algorithms.proofs.network-scoring`](../src/rainbow/algorithms/proofs/network_scoring.clj) | Additive scoring of a Bayesian network. |
| [`rainbow.algorithms.proofs.newton`](../src/rainbow/algorithms/proofs/newton.clj) | Newton's method as the general descent skeleton with a Hessian-inverse step size. |
| [`rainbow.algorithms.proofs.noisy-descent`](../src/rainbow/algorithms/proofs/noisy_descent.clj) | AHoF O38 Noisy Descent: the WRAP pattern that perturbs a base descent step with additive noise. |
| [`rainbow.algorithms.proofs.odd-monitor`](../src/rainbow/algorithms/proofs/odd_monitor.clj) | Operational Design Domain (ODD) monitoring over exact rationals (AHoF V59). |
| [`rainbow.algorithms.proofs.order-statistic`](../src/rainbow/algorithms/proofs/order_statistic.clj) | AHoF empirical rank / order statistic: the count of sample values that fall at or below a threshold, count-at-most t xs = \|{ x in xs : x <= t }\|, the unnormalized empirical CDF at t that underlies quantile estimation, ra |
| [`rainbow.algorithms.proofs.particle-swarm`](../src/rainbow/algorithms/proofs/particle_swarm.clj) | AHoF O45 Particle Swarm Optimization: the per-particle velocity and position update over genuinely n-dimensional vector state. |
| [`rainbow.algorithms.proofs.particle-swarm-best-iterate`](../src/rainbow/algorithms/proofs/particle_swarm_best_iterate.clj) | Finite-horizon best-so-far recurrence and objective monotonicity. |
| [`rainbow.algorithms.proofs.particle-swarm-convex-move`](../src/rainbow/algorithms/proofs/particle_swarm_convex_move.clj) | Normalized movement toward a swarm best preserves vector intervals. |
| [`rainbow.algorithms.proofs.particle-swarm-convex-trajectory`](../src/rainbow/algorithms/proofs/particle_swarm_convex_trajectory.clj) | Finite normalized consensus trajectories remain inside invariant intervals. |
| [`rainbow.algorithms.proofs.particle-swarm-global-best`](../src/rainbow/algorithms/proofs/particle_swarm_global_best.clj) | Verified finite-swarm global-best selection and best-so-far monotonicity. |
| [`rainbow.algorithms.proofs.particle-swarm-projected-trajectory`](../src/rainbow/algorithms/proofs/particle_swarm_projected_trajectory.clj) | Box-projected particle updates and finite-horizon trajectory boundedness. |
| [`rainbow.algorithms.proofs.path-relaxation`](../src/rainbow/algorithms/proofs/path_relaxation.clj) | AHoF shortest-path edge relaxation (the core step of Bellman-Ford and Dijkstra): when a candidate path of cost `alt` reaches a node whose current best cost is `current`, the tentative distance is relaxed to the smaller o |
| [`rainbow.algorithms.proofs.pattern-search`](../src/rainbow/algorithms/proofs/pattern_search.clj) | Generalized pattern search over exact rationals: a derivative-free poll that moves to the best of a set of candidate points. |
| [`rainbow.algorithms.proofs.penalty-method`](../src/rainbow/algorithms/proofs/penalty_method.clj) | AHoF O48 Penalty Method: the transform that turns a constrained problem into an unconstrained one by folding a penalty on constraint violation into the objective: augmented(x) = objective(x) + rho * penalty(x) where rho  |
| [`rainbow.algorithms.proofs.powell`](../src/rainbow/algorithms/proofs/powell.clj) | AHoF O33 Powell's Method: the conjugate search-direction generated from a cycle of coordinate line minimizations. |
| [`rainbow.algorithms.proofs.prefix-sum`](../src/rainbow/algorithms/proofs/prefix_sum.clj) | Cumulative sum (prefix-sum / scan): the running totals of a list, cumulative-sum [x0, x1, x2, ...] = [x0, x0+x1, x0+x1+x2, ...]. |
| [`rainbow.algorithms.proofs.reward-to-go`](../src/rainbow/algorithms/proofs/reward_to_go.clj) | AHoF D47 Reward-to-Go: the future-reward sum used by policy-gradient methods to reduce variance (REINFORCE uses the whole-trajectory return as the weight; reward-to-go replaces it with only the rewards from step t onward |
| [`rainbow.algorithms.proofs.rmsprop`](../src/rainbow/algorithms/proofs/rmsprop.clj) | AHoF O22 RMSProp: the decayed squared-gradient accumulator that adapts the learning rate. |
| [`rainbow.algorithms.proofs.robustness-objective`](../src/rainbow/algorithms/proofs/robustness_objective.clj) | The robustness-based falsification objective over signed rationals. |
| [`rainbow.algorithms.proofs.sarsa`](../src/rainbow/algorithms/proofs/sarsa.clj) | SARSA on-policy temporal-difference control over signed rationals. |
| [`rainbow.algorithms.proofs.simulated-annealing`](../src/rainbow/algorithms/proofs/simulated_annealing.clj) | AHoF O40 Simulated Annealing: the geometric temperature schedule and the deterministic (greedy-limit) Metropolis acceptance. |
| [`rainbow.algorithms.proofs.sparse-sampling`](../src/rainbow/algorithms/proofs/sparse_sampling.clj) | AHoF D35 Sparse Sampling: the sample-complexity count of the sparse-sampling MDP planner (Kearns-Mansour-Ng). |
| [`rainbow.algorithms.proofs.tournament-selection`](../src/rainbow/algorithms/proofs/tournament_selection.clj) | AHoF O43 Genetic Algorithm -- tournament selection operator: from a sampled tournament of candidate fitnesses the fittest (maximum) entrant is selected to reproduce. |
| [`rainbow.algorithms.proofs.triangular`](../src/rainbow/algorithms/proofs/triangular.clj) | AHoF triangular numbers T(n) = 0 + 1 + ... |
| [`rainbow.algorithms.proofs.trust-region`](../src/rainbow/algorithms/proofs/trust_region.clj) | Trust region step acceptance over exact rationals. |

## The Applied Higher-Order Functions catalogue (`src/rainbow/algorithms/proofs/ahof/`, 322)

| namespace | |
|---|---|
| [`rainbow.algorithms.proofs.ahof.ac-mcts`](../src/rainbow/algorithms/proofs/ahof/ac_mcts.clj) | AHoF D56 Actor-Critic with MCTS: guide tree search by the critic and select the child with the larger UCB-augmented value; it keeps the larger value: prefers-child-zero? |
| [`rainbow.algorithms.proofs.ahof.accuracy`](../src/rainbow/algorithms/proofs/ahof/accuracy.clj) | AHoF Classification Accuracy: the simplest evaluation metric -- the fraction of predictions that are correct, accuracy correct total = correct / total, a value in [0, 1]. |
| [`rainbow.algorithms.proofs.ahof.activity-selection`](../src/rainbow/algorithms/proofs/ahof/activity_selection.clj) | AHoF Activity Selection (greedy interval scheduling): from a set of activities with start and finish times, select the largest set of mutually compatible (non-overlapping) activities. |
| [`rainbow.algorithms.proofs.ahof.actor-critic`](../src/rainbow/algorithms/proofs/ahof/actor_critic.clj) | AHoF D53 Actor-Critic: the critic bootstraps a temporal-difference target from the immediate reward plus the discounted value of the next state, and the actor is updated toward it. |
| [`rainbow.algorithms.proofs.ahof.adaboost`](../src/rainbow/algorithms/proofs/ahof/adaboost.clj) | AHoF AdaBoost (Adaptive Boosting): combine many weak classifiers into a strong one by a weighted majority vote, where each weak learner's vote weight alpha = (1/2) ln((1 - err)/err) DECREASES with its weighted error err  |
| [`rainbow.algorithms.proofs.ahof.adaptive-is`](../src/rainbow/algorithms/proofs/ahof/adaptive_is.clj) | AHoF V28 Adaptive Importance Sampling: iteratively refine the proposal and reweight samples by the ratio of the target density to the current proposal density: reweight target proposal = target / proposal. |
| [`rainbow.algorithms.proofs.ahof.agent-model`](../src/rainbow/algorithms/proofs/ahof/agent_model.clj) | AHoF V3 Agent Model Construction: fit a model of another agent's behaviour; the model fits when its prediction error is within the tolerance: model-fits? |
| [`rainbow.algorithms.proofs.ahof.alpha-vector`](../src/rainbow/algorithms/proofs/ahof/alpha_vector.clj) | AHoF D71 Alpha Vector (Exact POMDP value function): the optimal value at a belief b is the maximum over the alpha-vector set of the inner products <alpha, b>. |
| [`rainbow.algorithms.proofs.ahof.articulation-points`](../src/rainbow/algorithms/proofs/ahof/articulation_points.clj) | AHoF Articulation Points (Tarjan's DFS low-link algorithm): find the cut vertices of an undirected graph -- those whose removal disconnects it -- in O(V + E), the basis of network-reliability and bridge analysis. |
| [`rainbow.algorithms.proofs.ahof.astar`](../src/rainbow/algorithms/proofs/ahof/astar.clj) | AHoF D37 A* / heuristic search: the priority by which A* expands nodes is the estimated total cost through a node, the path cost so far plus the heuristic estimate of the cost to go: f g h = g + h over exact-rational cos |
| [`rainbow.algorithms.proofs.ahof.astar-falsification`](../src/rainbow/algorithms/proofs/ahof/astar_falsification.clj) | AHoF V18 A* for Falsification: search the space of system behaviours for a specification violation using A*, ordering the frontier by the f-cost f = g + h (the cost so far plus an admissible heuristic to a likely violati |
| [`rainbow.algorithms.proofs.ahof.async-value-iteration`](../src/rainbow/algorithms/proofs/ahof/async_value_iteration.clj) | AHoF D23 worked asynchronous (Gauss-Seidel) value-iteration instance. |
| [`rainbow.algorithms.proofs.ahof.backtracking`](../src/rainbow/algorithms/proofs/ahof/backtracking.clj) | AHoF O14 Backtracking Line Search: shrink the step until the Armijo sufficient- decrease condition holds -- the new objective is at or below the predicted decrease bound f(x) + c*alpha*slope: sufficient-decrease? |
| [`rainbow.algorithms.proofs.ahof.baseline-subtraction`](../src/rainbow/algorithms/proofs/ahof/baseline_subtraction.clj) | AHoF D48 Baseline Subtraction: the variance-reduction wrapper for policy-gradient estimators. |
| [`rainbow.algorithms.proofs.ahof.bayes-adaptive-mdp`](../src/rainbow/algorithms/proofs/ahof/bayes_adaptive_mdp.clj) | AHoF D60 Bayes-Adaptive MDP: plan in the belief-MDP over unknown model parameters, where the value of an action is the posterior-belief-weighted average of its value under each candidate model: expected-value b0 v0 b1 v1 |
| [`rainbow.algorithms.proofs.ahof.bayes-net`](../src/rainbow/algorithms/proofs/ahof/bayes_net.clj) | AHoF D1 Bayesian Network Representation: the joint distribution factorizes as a\n product of conditional-probability factors; the joint mass of two factors is their\n product joint-factor a b = a * b. |
| [`rainbow.algorithms.proofs.ahof.bayes-theorem`](../src/rainbow/algorithms/proofs/ahof/bayes_theorem.clj) | AHoF Bayes' Theorem: invert a conditional probability to obtain the posterior belief in a hypothesis H after observing evidence E, posterior likelihood prior evidence = (likelihood * prior) / evidence i.e. |
| [`rainbow.algorithms.proofs.ahof.bayesian-learning`](../src/rainbow/algorithms/proofs/ahof/bayesian_learning.clj) | AHoF D11 worked Bayesian parameter learning over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.bayesian-model-estimation`](../src/rainbow/algorithms/proofs/ahof/bayesian_model_estimation.clj) | AHoF D59 Bayesian Model Estimation: score candidate models by their posterior probability, which is proportional to the data likelihood under the model times the model prior: posterior-score likelihood prior = likelihood |
| [`rainbow.algorithms.proofs.ahof.bayesian-opt`](../src/rainbow/algorithms/proofs/ahof/bayesian_opt.clj) | Kochenderfer surrogate-optimization / model-validation cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: O19.1 probability of improvement : acquisition prefers candidates bea |
| [`rainbow.algorithms.proofs.ahof.bayesian-optimization`](../src/rainbow/algorithms/proofs/ahof/bayesian_optimization.clj) | AHoF O65 Bayesian Optimization Loop: iterate (fit surrogate -> maximize acquisition -> evaluate) and track the best observation seen. |
| [`rainbow.algorithms.proofs.ahof.bayesian-param`](../src/rainbow/algorithms/proofs/ahof/bayesian_param.clj) | AHoF V2 Bayesian Parameter Learning: infer model parameters by their posterior, which is proportional to the data likelihood under the parameter times the parameter prior: posterior-score likelihood prior = likelihood *  |
| [`rainbow.algorithms.proofs.ahof.beam-search`](../src/rainbow/algorithms/proofs/ahof/beam_search.clj) | AHoF D-family Beam Search: a bounded-breadth heuristic search that, at each level, expands only the K highest-scoring partial solutions (the beam) instead of the full frontier -- trading completeness for tractable memory |
| [`rainbow.algorithms.proofs.ahof.behavioral-cloning`](../src/rainbow/algorithms/proofs/ahof/behavioral_cloning.clj) | AHoF D64 Behavioral Cloning (imitation learning): train a policy by supervised learning to reproduce an expert's actions, minimizing an imitation loss. |
| [`rainbow.algorithms.proofs.ahof.belief-propagation`](../src/rainbow/algorithms/proofs/ahof/belief_propagation.clj) | AHoF D4 Sum-Product (Belief Propagation): approximate marginal inference by passing messages on the factor graph until convergence. |
| [`rainbow.algorithms.proofs.ahof.bellman-ford`](../src/rainbow/algorithms/proofs/ahof/bellman_ford.clj) | AHoF Bellman-Ford single-source shortest paths: unlike Dijkstra, it handles edges of any (including negative) weight by relaxing EVERY edge repeatedly for V-1 passes, and detects a negative-weight cycle if some edge stil |
| [`rainbow.algorithms.proofs.ahof.bfgs`](../src/rainbow/algorithms/proofs/ahof/bfgs.clj) | AHoF O29 BFGS: a quasi-Newton method whose Hessian-approximation update uses the\n gradient change y = g_{k+1} - g_k: gradient-change g-new g-old = g-new - g-old.\n Worked: 4-1=3. |
| [`rainbow.algorithms.proofs.ahof.bfs-reachability`](../src/rainbow/algorithms/proofs/ahof/bfs_reachability.clj) | AHoF V48 BFS/DFS Graph Reachability: explore the state graph to decide whether a target is reachable; a state is within the explored frontier when its distance to the frontier representative is within the radius: reachab |
| [`rainbow.algorithms.proofs.ahof.bin-packing`](../src/rainbow/algorithms/proofs/ahof/bin_packing.clj) | AHoF Bin Packing (First-Fit approximation): pack items of given sizes into the fewest unit-capacity bins. |
| [`rainbow.algorithms.proofs.ahof.binary-heap`](../src/rainbow/algorithms/proofs/ahof/binary_heap.clj) | AHoF Binary Heap: the array-backed complete binary tree behind the priority queue and heapsort, maintaining the HEAP PROPERTY -- in a min-heap every parent key is at most its children's keys, so the minimum is always at  |
| [`rainbow.algorithms.proofs.ahof.binary-search`](../src/rainbow/algorithms/proofs/ahof/binary_search.clj) | AHoF Binary Search: locate a target in a SORTED array in O(log n) by repeatedly halving the search interval -- comparing the target to the middle element and discarding the half that cannot contain it. |
| [`rainbow.algorithms.proofs.ahof.bipartite-matching`](../src/rainbow/algorithms/proofs/ahof/bipartite_matching.clj) | AHoF Maximum Bipartite Matching (augmenting-path / Hungarian tree method): find the largest set of edges with no shared endpoints in a bipartite graph -- the model for job/worker assignment, scheduling, and network routi |
| [`rainbow.algorithms.proofs.ahof.bisection`](../src/rainbow/algorithms/proofs/ahof/bisection.clj) | AHoF O12 worked bisection bracket search over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.bloom-filter`](../src/rainbow/algorithms/proofs/ahof/bloom_filter.clj) | AHoF Bloom Filter: a space-efficient probabilistic set that answers membership with NO FALSE NEGATIVES (if it says absent, the element was never added) but possible false positives. |
| [`rainbow.algorithms.proofs.ahof.boyer-moore`](../src/rainbow/algorithms/proofs/ahof/boyer_moore.clj) | AHoF Boyer-Moore Majority Vote: find the element that appears MORE than n/2 times (if one exists) in O(n) time and O(1) space -- a single streaming pass that keeps just a candidate and a counter, incrementing on a match  |
| [`rainbow.algorithms.proofs.ahof.branch-and-bound`](../src/rainbow/algorithms/proofs/ahof/branch_and_bound.clj) | AHoF D34 worked Branch and Bound pruning step over exact rationals, reusing the shared bounding lemma (rainbow.algorithms.proofs.branch-and-bound, branch-and-bound/*). |
| [`rainbow.algorithms.proofs.ahof.bucket-sort`](../src/rainbow/algorithms/proofs/ahof/bucket_sort.clj) | AHoF Bucket Sort: sort values drawn from a uniform range in EXPECTED linear time by distributing them into ordered buckets by value, sorting each bucket (with any comparison sort), and CONCATENATING the buckets in order. |
| [`rainbow.algorithms.proofs.ahof.ce-falsification`](../src/rainbow/algorithms/proofs/ahof/ce_falsification.clj) | AHoF V15 Cross-Entropy for Falsification: fit the sampling distribution to the failure region by keeping the elite (lowest-cost) samples below the cross-entropy quantile: elite? |
| [`rainbow.algorithms.proofs.ahof.central-difference`](../src/rainbow/algorithms/proofs/ahof/central_difference.clj) | AHoF O2 Central Difference: the central finite difference estimates a derivative as (f(x+h) - f(x-h)) / (2h). |
| [`rainbow.algorithms.proofs.ahof.chebyshev-scalarization`](../src/rainbow/algorithms/proofs/ahof/chebyshev_scalarization.clj) | AHoF multi-objective method: weighted-Chebyshev (max-norm) scalarization. |
| [`rainbow.algorithms.proofs.ahof.christofides`](../src/rainbow/algorithms/proofs/ahof/christofides.clj) | AHoF Christofides Algorithm: the best-known polynomial APPROXIMATION for the metric Travelling Salesman Problem. |
| [`rainbow.algorithms.proofs.ahof.clamped-surrogate`](../src/rainbow/algorithms/proofs/ahof/clamped_surrogate.clj) | AHoF D52 Clamped Surrogate Objective (PPO): stabilize policy-gradient updates by clamping the probability ratio r into the trust region [lo, hi] = [1-eps, 1+eps] before forming the surrogate objective: clamp r lo hi = mi |
| [`rainbow.algorithms.proofs.ahof.cmaes`](../src/rainbow/algorithms/proofs/ahof/cmaes.clj) | AHoF O42 CMA-ES (Covariance Matrix Adaptation Evolution Strategy) -- the mean recombination step. |
| [`rainbow.algorithms.proofs.ahof.cmaes-falsification`](../src/rainbow/algorithms/proofs/ahof/cmaes_falsification.clj) | AHoF V14 CMA-ES for Falsification: adapt a Gaussian search distribution toward the failure region using the elite (lowest-cost) samples; a sample is elite when its cost is within the elite quantile: elite? |
| [`rainbow.algorithms.proofs.ahof.coin-change`](../src/rainbow/algorithms/proofs/ahof/coin_change.clj) | AHoF Coin Change (dynamic programming): the minimum number of coins that sum to a target amount, from unlimited coins of given denominations -- the canonical unbounded-knapsack-style min-DP. |
| [`rainbow.algorithms.proofs.ahof.column-generation`](../src/rainbow/algorithms/proofs/ahof/column_generation.clj) | AHoF O-family Column Generation: solve a large linear program with too many variables to enumerate by working with a small RESTRICTED master problem and generating new columns only as needed. |
| [`rainbow.algorithms.proofs.ahof.complex-step`](../src/rainbow/algorithms/proofs/ahof/complex_step.clj) | AHoF O3 Complex-Step Derivative (classical method: f'(x) ~ Im f(x + ih) / h, which avoids subtractive cancellation). |
| [`rainbow.algorithms.proofs.ahof.composite-metric`](../src/rainbow/algorithms/proofs/ahof/composite_metric.clj) | AHoF V5 worked composite metric over exact rationals, combining an accuracy of 3/4 and a precision of 1/4. |
| [`rainbow.algorithms.proofs.ahof.concrete-reachability`](../src/rainbow/algorithms/proofs/ahof/concrete_reachability.clj) | AHoF V44 Concrete Reachability: the simplest reachability analysis -- push a finite set of concrete sample states one step forward through the dynamics and collect the images. |
| [`rainbow.algorithms.proofs.ahof.confidence-interval`](../src/rainbow/algorithms/proofs/ahof/confidence_interval.clj) | AHoF Confidence Interval: quantify the uncertainty of a point estimate by an interval that, over repeated sampling, covers the true parameter with a chosen confidence level (e.g. |
| [`rainbow.algorithms.proofs.ahof.conformal`](../src/rainbow/algorithms/proofs/ahof/conformal.clj) | AHoF Conformal Prediction: a distribution-free method that turns any point predictor into set-valued predictions with a finite-sample coverage guarantee. |
| [`rainbow.algorithms.proofs.ahof.conjugate-gradient`](../src/rainbow/algorithms/proofs/ahof/conjugate_gradient.clj) | AHoF O18 worked conjugate gradient over signed rationals with pair state. |
| [`rainbow.algorithms.proofs.ahof.constrained-ls`](../src/rainbow/algorithms/proofs/ahof/constrained_ls.clj) | Kochenderfer 'Algorithms for Optimization' Ch.11/13 constrained least-squares / distributed cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: O13.2 least squares w/ inequalit |
| [`rainbow.algorithms.proofs.ahof.coordinate-search`](../src/rainbow/algorithms/proofs/ahof/coordinate_search.clj) | AHoF O32 worked cyclic coordinate search over signed-rational pair state. |
| [`rainbow.algorithms.proofs.ahof.correlated-equilibrium`](../src/rainbow/algorithms/proofs/ahof/correlated_equilibrium.clj) | AHoF D78 Correlated Equilibrium: a distribution over joint action profiles from which no player has an incentive to deviate from the mediator's recommendation; the per-player adherence test compares a deviation payoff ag |
| [`rainbow.algorithms.proofs.ahof.cosine-similarity`](../src/rainbow/algorithms/proofs/ahof/cosine_similarity.clj) | AHoF Cosine Similarity: measure the similarity of two vectors by the cosine of the angle between them -- the dot product normalized by the product of their magnitudes, cosine dot-product magnitude-product = (a . |
| [`rainbow.algorithms.proofs.ahof.counterfactual-cf`](../src/rainbow/algorithms/proofs/ahof/counterfactual_cf.clj) | AHoF V57 Counterfactual Explanation: explain a model decision by the smallest change to the input that flips the prediction to a desired class. |
| [`rainbow.algorithms.proofs.ahof.counting-sort`](../src/rainbow/algorithms/proofs/ahof/counting_sort.clj) | AHoF Counting Sort: a stable, NON-comparison, O(n + k) sort for integer keys in a small range [0, k). |
| [`rainbow.algorithms.proofs.ahof.cross-entropy`](../src/rainbow/algorithms/proofs/ahof/cross_entropy.clj) | AHoF O41 Cross-Entropy Method: a model-based stochastic optimizer that, each iteration, samples a population, keeps the top-scoring ELITE, and refits the sampling distribution to the elite. |
| [`rainbow.algorithms.proofs.ahof.cross-entropy-is`](../src/rainbow/algorithms/proofs/ahof/cross_entropy_is.clj) | AHoF V29 Cross-Entropy Importance Sampling: iteratively fit the sampling distribution to the rare failure region by keeping the elite samples -- those whose cost falls at or below the current elite quantile threshold: el |
| [`rainbow.algorithms.proofs.ahof.cross-validation`](../src/rainbow/algorithms/proofs/ahof/cross_validation.clj) | AHoF V4 worked cross-validation over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.cutting-planes`](../src/rainbow/algorithms/proofs/ahof/cutting_planes.clj) | AHoF O73 Cutting Planes: solve an integer/convex program by iteratively adding linear inequalities (cuts) that remove the current fractional/infeasible LP solution while preserving all true solutions. |
| [`rainbow.algorithms.proofs.ahof.cyk`](../src/rainbow/algorithms/proofs/ahof/cyk.clj) | AHoF CYK Algorithm (Cocke-Younger-Kasami): decide whether a string is generated by a context-free grammar in Chomsky Normal Form, in O(n^3 * \|G\|), by dynamic programming over substrings. |
| [`rainbow.algorithms.proofs.ahof.dagger`](../src/rainbow/algorithms/proofs/ahof/dagger.clj) | AHoF D65 DAgger (Dataset Aggregation for imitation learning): iteratively run the current policy, query the expert to label the visited states, and aggregate; the expert is queried when the policy's uncertainty reaches a |
| [`rainbow.algorithms.proofs.ahof.dbscan`](../src/rainbow/algorithms/proofs/ahof/dbscan.clj) | AHoF DBSCAN (Density-Based Spatial Clustering of Applications with Noise): find clusters of arbitrary shape as dense regions separated by sparse ones, labelling low-density points as noise -- without needing the number o |
| [`rainbow.algorithms.proofs.ahof.dcp`](../src/rainbow/algorithms/proofs/ahof/dcp.clj) | AHoF O57 Disciplined Convex Programming: express a convex program from a grammar of convex atoms so feasibility of each convex inequality constraint g(x) <= b reduces to a decidable exact-rational comparison of the const |
| [`rainbow.algorithms.proofs.ahof.dec-pomdp-dp`](../src/rainbow/algorithms/proofs/ahof/dec_pomdp_dp.clj) | AHoF D82 Dec-POMDP (Dynamic Programming): back up joint-policy values, keeping the larger of two candidate joint-policy values: prefers-joint-zero? |
| [`rainbow.algorithms.proofs.ahof.dec-pomdp-hs`](../src/rainbow/algorithms/proofs/ahof/dec_pomdp_hs.clj) | AHoF D83 Dec-POMDP Heuristic Search: search the space of joint policies with heuristic bounds; converged when the bound gap is within precision: converged? |
| [`rainbow.algorithms.proofs.ahof.decision-network`](../src/rainbow/algorithms/proofs/ahof/decision_network.clj) | AHoF D18 worked decision network evaluation over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.decision-tree`](../src/rainbow/algorithms/proofs/ahof/decision_tree.clj) | AHoF D-family Decision Tree learning (greedy top-down induction): at each node, split on the feature that most improves purity -- i.e. |
| [`rainbow.algorithms.proofs.ahof.deterministic-pg`](../src/rainbow/algorithms/proofs/ahof/deterministic_pg.clj) | AHoF D55 Deterministic Policy Gradient: the DPG theorem gives the gradient as the\n chain product of the action-value gradient and the policy Jacobian, grad =\n \u2207_a Q \u00b7 \u2207_\u03b8 \u03bc: policy-gradient q-g |
| [`rainbow.algorithms.proofs.ahof.dfp`](../src/rainbow/algorithms/proofs/ahof/dfp.clj) | AHoF O28 DFP (Davidon-Fletcher-Powell): a quasi-Newton method whose curvature update\n uses the step vector s = x_{k+1} - x_k: step-vector x-new x-old = x-new - x-old.\n Worked: 3-1=2. |
| [`rainbow.algorithms.proofs.ahof.dijkstra`](../src/rainbow/algorithms/proofs/ahof/dijkstra.clj) | AHoF Dijkstra's Shortest Path: single-source shortest paths on a graph with NON-NEGATIVE edge weights. |
| [`rainbow.algorithms.proofs.ahof.direct`](../src/rainbow/algorithms/proofs/ahof/direct.clj) | AHoF O37 DIRECT (DIvided RECTangles): a Lipschitzian global optimizer that partitions the domain into rectangles and subdivides the 'potentially optimal' ones. |
| [`rainbow.algorithms.proofs.ahof.direct-sampling`](../src/rainbow/algorithms/proofs/ahof/direct_sampling.clj) | AHoF D5 Direct Sampling: draw a sample from a Bayesian network by ancestral sampling, drawing each variable from its conditional distribution given already sampled parents. |
| [`rainbow.algorithms.proofs.ahof.discrete-filter`](../src/rainbow/algorithms/proofs/ahof/discrete_filter.clj) | AHoF D66 Discrete State Filter (recursive Bayesian filtering over a finite state space): each step multiplies the prior belief in a state by the measurement likelihood to get the unnormalized posterior weight, then renor |
| [`rainbow.algorithms.proofs.ahof.discrete-search`](../src/rainbow/algorithms/proofs/ahof/discrete_search.clj) | Kochenderfer discrete-search / sampling / metaheuristic cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: O22.7 0-1 knapsack DP : cell = max(exclude value, include value) V5. |
| [`rainbow.algorithms.proofs.ahof.disturbance-falsification`](../src/rainbow/algorithms/proofs/ahof/disturbance_falsification.clj) | AHoF V10 Disturbance-Based Falsification: search bounded disturbances to drive the system to a violation; a violation is found when the achieved robustness drops to or below the margin: violation? |
| [`rainbow.algorithms.proofs.ahof.dual-simplex`](../src/rainbow/algorithms/proofs/ahof/dual_simplex.clj) | AHoF O55 Dual Simplex Method: solve a linear program by maintaining DUAL feasibility (reduced costs of the right sign) while iterating toward primal feasibility. |
| [`rainbow.algorithms.proofs.ahof.dutch-flag`](../src/rainbow/algorithms/proofs/ahof/dutch_flag.clj) | AHoF Dutch National Flag (Dijkstra's 3-way partition): partition an array around a pivot into three regions -- less than, equal to, and greater than -- in a single O(n) pass with O(1) extra space. |
| [`rainbow.algorithms.proofs.ahof.edmonds-karp`](../src/rainbow/algorithms/proofs/ahof/edmonds_karp.clj) | AHoF Edmonds-Karp Algorithm: compute the maximum flow through a network in O(V*E^2) by repeatedly finding a SHORTEST augmenting path (by BFS) in the residual graph and pushing flow along it, until none remains -- a concr |
| [`rainbow.algorithms.proofs.ahof.ekf`](../src/rainbow/algorithms/proofs/ahof/ekf.clj) | AHoF D68 Extended Kalman Filter: the EKF linearizes the nonlinear process and measurement models about the current estimate and applies the standard Kalman measurement update, blending the prediction with the observation |
| [`rainbow.algorithms.proofs.ahof.eligibility-traces`](../src/rainbow/algorithms/proofs/ahof/eligibility_traces.clj) | AHoF D63 worked eligibility traces (TD(lambda)) over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.ellipsoid`](../src/rainbow/algorithms/proofs/ahof/ellipsoid.clj) | AHoF V36 Ellipsoid Propagation: over-approximate a reachable set by an ellipsoid; a point lies inside when its quadratic form (x-c)'P(x-c) is within the ellipsoid limit: in-ellipsoid? |
| [`rainbow.algorithms.proofs.ahof.em`](../src/rainbow/algorithms/proofs/ahof/em.clj) | AHoF D13 EM Algorithm: fit latent-variable model parameters by alternating an E-step (compute the expected complete-data log-likelihood under the current parameters) and an M-step (maximize it). |
| [`rainbow.algorithms.proofs.ahof.ensemble-disagreement`](../src/rainbow/algorithms/proofs/ahof/ensemble_disagreement.clj) | AHoF V61 Ensemble Disagreement: quantify predictive uncertainty by the spread of an ensemble's predictions and flag an input as uncertain when the disagreement reaches a threshold: flag-uncertain? |
| [`rainbow.algorithms.proofs.ahof.epsilon-constraint`](../src/rainbow/algorithms/proofs/ahof/epsilon_constraint.clj) | AHoF O67 Epsilon-Constraint Method (multi-objective): optimize one objective while the others are turned into inequality constraints f_i <= epsilon_i. |
| [`rainbow.algorithms.proofs.ahof.epsilon-greedy`](../src/rainbow/algorithms/proofs/ahof/epsilon_greedy.clj) | AHoF epsilon-greedy exploration: the canonical explore/exploit rule for bandits and reinforcement learning. |
| [`rainbow.algorithms.proofs.ahof.exact-inference`](../src/rainbow/algorithms/proofs/ahof/exact_inference.clj) | AHoF D2 worked exact Bayesian inference by enumeration. |
| [`rainbow.algorithms.proofs.ahof.expected-improvement`](../src/rainbow/algorithms/proofs/ahof/expected_improvement.clj) | AHoF O63 Expected Improvement acquisition (Bayesian optimization). |
| [`rainbow.algorithms.proofs.ahof.exploration-strategies`](../src/rainbow/algorithms/proofs/ahof/exploration_strategies.clj) | Kochenderfer 'Algorithms for Decision Making' Ch.15 bandit exploration strategies, expressed as higher-order-function compositions and proved axiom-free (core structural property per algorithm), extending the 222 AHoF ca |
| [`rainbow.algorithms.proofs.ahof.f1-score`](../src/rainbow/algorithms/proofs/ahof/f1_score.clj) | AHoF F1 Score: the standard single-number summary of a classifier's quality on imbalanced data -- the HARMONIC MEAN of precision and recall, f1 precision recall = 2 * precision * recall / (precision + recall). |
| [`rainbow.algorithms.proofs.ahof.failure-mode`](../src/rainbow/algorithms/proofs/ahof/failure_mode.clj) | AHoF V58 Failure Mode Characterization: cluster observed failures into modes and assign a new failure to a mode when its distance to the mode's centroid is within the mode radius: in-mode? |
| [`rainbow.algorithms.proofs.ahof.failure-probability-monitor`](../src/rainbow/algorithms/proofs/ahof/failure_probability_monitor.clj) | AHoF V64 worked failure-probability monitor over exact rationals with risk threshold 1/2. |
| [`rainbow.algorithms.proofs.ahof.falsification`](../src/rainbow/algorithms/proofs/ahof/falsification.clj) | AHoF V9 Direct Sampling Falsification: the simplest falsification method -- sample inputs, simulate, and return the first whose specification robustness has dropped to the falsification margin. |
| [`rainbow.algorithms.proofs.ahof.falsification-opt`](../src/rainbow/algorithms/proofs/ahof/falsification_opt.clj) | AHoF V12 Falsification as Optimization: cast falsification as minimizing the STL robustness of the specification over inputs; a violation is found when the achieved robustness drops to or below the violation margin: viol |
| [`rainbow.algorithms.proofs.ahof.feasibility`](../src/rainbow/algorithms/proofs/ahof/feasibility.clj) | Constraint feasibility checking (the conjunctive dual of the SAT clause and the model-checking companion of V50): a candidate is feasible when ALL of its constraints are satisfied. |
| [`rainbow.algorithms.proofs.ahof.fenwick-tree`](../src/rainbow/algorithms/proofs/ahof/fenwick_tree.clj) | AHoF Fenwick Tree (Binary Indexed Tree): maintain prefix sums of an array under point updates, both in O(log n), using a clever low-bit indexing where each index is responsible for a range of size equal to its lowest set |
| [`rainbow.algorithms.proofs.ahof.fibonacci-search`](../src/rainbow/algorithms/proofs/ahof/fibonacci_search.clj) | AHoF O8 worked Fibonacci Search reduction step over exact rationals, reusing the shared bracket-reduction lemma (rainbow.algorithms.proofs.golden-section-search, linesearch/*). |
| [`rainbow.algorithms.proofs.ahof.fictitious-play`](../src/rainbow/algorithms/proofs/ahof/fictitious_play.clj) | AHoF D79 Fictitious Play: in a repeated game each player best-responds to the empirical frequency of the opponent's past actions. |
| [`rainbow.algorithms.proofs.ahof.finite-state-controller`](../src/rainbow/algorithms/proofs/ahof/finite_state_controller.clj) | AHoF D76 Finite State Controller: a POMDP policy as a finite-state machine; at a controller node it selects the higher-value action; it keeps the larger value: prefers-action-zero? |
| [`rainbow.algorithms.proofs.ahof.fisher-yates`](../src/rainbow/algorithms/proofs/ahof/fisher_yates.clj) | AHoF Fisher-Yates Shuffle (Knuth shuffle): produce a UNIFORMLY RANDOM permutation of an array in O(n) time in place -- every one of the n! |
| [`rainbow.algorithms.proofs.ahof.floyd-cycle`](../src/rainbow/algorithms/proofs/ahof/floyd_cycle.clj) | AHoF Floyd's Cycle Detection (tortoise and hare): detect a cycle in a linked list or a functional sequence x_{n+1} = f(x_n) in O(1) extra space, by advancing a SLOW pointer one step and a FAST pointer two steps per itera |
| [`rainbow.algorithms.proofs.ahof.forward-difference`](../src/rainbow/algorithms/proofs/ahof/forward_difference.clj) | AHoF O1 Forward Difference: approximate a derivative by the forward finite difference (f(x+h) - f(x)) / h. |
| [`rainbow.algorithms.proofs.ahof.forward-mode-ad`](../src/rainbow/algorithms/proofs/ahof/forward_mode_ad.clj) | AHoF O4 Forward-Mode Auto-Diff: propagate derivatives through a computation with dual\n numbers; the chain rule composes derivatives multiplicatively (f\u2218g)'=f'(g)\u00b7g':\n dual-derivative outer-deriv inner-deriv = |
| [`rainbow.algorithms.proofs.ahof.forward-reachability`](../src/rainbow/algorithms/proofs/ahof/forward_reachability.clj) | AHoF V33 Forward Reachability: over-approximate the set of states reachable from an initial set by forward-propagating an enclosure; a state is in the forward-reachable over-approximation when its distance to the reachab |
| [`rainbow.algorithms.proofs.ahof.forward-search`](../src/rainbow/algorithms/proofs/ahof/forward_search.clj) | AHoF D33 Forward Search: finite-horizon lookahead planning. |
| [`rainbow.algorithms.proofs.ahof.fractional-knapsack`](../src/rainbow/algorithms/proofs/ahof/fractional_knapsack.clj) | AHoF Fractional Knapsack: unlike the 0/1 version (which needs DP), when items may be taken in fractional amounts the problem is solved OPTIMALLY by a simple greedy rule -- take items in decreasing order of value density  |
| [`rainbow.algorithms.proofs.ahof.frank-wolfe`](../src/rainbow/algorithms/proofs/ahof/frank_wolfe.clj) | AHoF O-family Frank-Wolfe (Conditional Gradient) method: minimize a convex objective over a convex set WITHOUT projections. |
| [`rainbow.algorithms.proofs.ahof.fuzzing`](../src/rainbow/algorithms/proofs/ahof/fuzzing.clj) | AHoF V11 Fuzzing: generate test inputs by repeatedly mutating a seed input and checking whether any mutant violates the specification. |
| [`rainbow.algorithms.proofs.ahof.ga-policy`](../src/rainbow/algorithms/proofs/ahof/ga_policy.clj) | AHoF D41 GA for Policy Search: evolve policies under fitness selection, keeping the fitter individual: prefers-fitter? |
| [`rainbow.algorithms.proofs.ahof.gae`](../src/rainbow/algorithms/proofs/ahof/gae.clj) | AHoF D42 Generalized Advantage Estimation: estimate the advantage function as an exponentially-weighted (by gamma*lambda) sum of temporal-difference errors, A_t = delta_t + (gamma*lambda) delta_{t+1} + (gamma*lambda)^2 d |
| [`rainbow.algorithms.proofs.ahof.gae54`](../src/rainbow/algorithms/proofs/ahof/gae54.clj) | AHoF D54 Generalized Advantage Estimation: form a low-variance advantage estimate as an exponentially-weighted sum of one-step TD residuals; the recursive form combines the current residual with the discounted future adv |
| [`rainbow.algorithms.proofs.ahof.game-ascent`](../src/rainbow/algorithms/proofs/ahof/game_ascent.clj) | AHoF D80 Gradient Ascent (Games): each player ascends its own payoff gradient,\n updating ascent-step theta step = theta + step. |
| [`rainbow.algorithms.proofs.ahof.game-equilibria`](../src/rainbow/algorithms/proofs/ahof/game_equilibria.clj) | Kochenderfer 'Algorithms for Decision Making' Ch.24-27 multi-agent equilibrium cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog. |
| [`rainbow.algorithms.proofs.ahof.gas-station`](../src/rainbow/algorithms/proofs/ahof/gas_station.clj) | AHoF Gas Station (greedy circular tour): around a circle of stations, station i provides gas[i] and it costs cost[i] to drive to the next. |
| [`rainbow.algorithms.proofs.ahof.gauss-seidel`](../src/rainbow/algorithms/proofs/ahof/gauss_seidel.clj) | Gauss-Seidel coordinate update (Kochenderfer Optimization O24.1), the last of the four signed-cluster algorithms deferred in August. |
| [`rainbow.algorithms.proofs.ahof.gaussian-inference`](../src/rainbow/algorithms/proofs/ahof/gaussian_inference.clj) | AHoF D9 Inference in Gaussian Models: exact closed-form conjugate updates. |
| [`rainbow.algorithms.proofs.ahof.gaussian-process`](../src/rainbow/algorithms/proofs/ahof/gaussian_process.clj) | AHoF O62 Gaussian Process (surrogate model / regression): the GP posterior mean at a query point is a kernel-weighted combination of the observed targets, the weights coming from the covariance between the query and the  |
| [`rainbow.algorithms.proofs.ahof.general-descent`](../src/rainbow/algorithms/proofs/ahof/general_descent.clj) | AHoF O13 worked general descent, instantiated to gradient descent. |
| [`rainbow.algorithms.proofs.ahof.genetic-programming`](../src/rainbow/algorithms/proofs/ahof/genetic_programming.clj) | AHoF O70 Genetic Programming: evolve programs represented as expression trees under fitness selection; between two candidate programs it keeps the fitter (higher- fitness) one: prefers-fitter? |
| [`rainbow.algorithms.proofs.ahof.gibbs`](../src/rainbow/algorithms/proofs/ahof/gibbs.clj) | AHoF D8 Gibbs Sampling: an MCMC method that samples a joint distribution by repeatedly resampling one coordinate at a time from its full conditional given all the others. |
| [`rainbow.algorithms.proofs.ahof.gibbs-failures`](../src/rainbow/algorithms/proofs/ahof/gibbs_failures.clj) | AHoF V23 Gibbs Sampling (Failures): reuse the Gibbs structure over the failure region, resampling each variable from its full conditional; the draw is from the conditional when the uniform sample falls under the conditio |
| [`rainbow.algorithms.proofs.ahof.gini-impurity`](../src/rainbow/algorithms/proofs/ahof/gini_impurity.clj) | AHoF Gini Impurity: the node-purity criterion used by CART decision trees (and a cheaper alternative to entropy). |
| [`rainbow.algorithms.proofs.ahof.golden-section-search`](../src/rainbow/algorithms/proofs/ahof/golden_section_search.clj) | AHoF O9 worked Golden Section Search reduction step over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.gradient-ascent`](../src/rainbow/algorithms/proofs/ahof/gradient_ascent.clj) | AHoF D49 worked bounded fixed-rate gradient-ascent instance. |
| [`rainbow.algorithms.proofs.ahof.gradient-boosting`](../src/rainbow/algorithms/proofs/ahof/gradient_boosting.clj) | AHoF Gradient Boosting (GBM / the core of XGBoost, LightGBM): build a strong predictor as an additive ensemble, where each stage fits a weak learner (usually a shallow tree) to the negative gradient of the loss (the resi |
| [`rainbow.algorithms.proofs.ahof.gradient-clipping`](../src/rainbow/algorithms/proofs/ahof/gradient_clipping.clj) | AHoF Gradient Clipping (clip-by-norm): stabilize the training of deep and recurrent networks by capping the gradient's magnitude, preventing the exploding-gradient problem where a single huge update destroys the model. |
| [`rainbow.algorithms.proofs.ahof.gradient-descent`](../src/rainbow/algorithms/proofs/ahof/gradient_descent.clj) | AHoF O17 worked bounded gradient descent over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.grammatical-evolution`](../src/rainbow/algorithms/proofs/ahof/grammatical_evolution.clj) | AHoF O71 Grammatical Evolution: evolve programs by mapping integer genomes through a BNF grammar, then select by fitness; between two individuals it keeps the fitter one: prefers-fitter? |
| [`rainbow.algorithms.proofs.ahof.graph-coloring`](../src/rainbow/algorithms/proofs/ahof/graph_coloring.clj) | AHoF Greedy Graph Coloring: assign colors to vertices so no edge joins two of the same color, using few colors -- the model for register allocation, exam scheduling, and frequency assignment. |
| [`rainbow.algorithms.proofs.ahof.greedy-policy`](../src/rainbow/algorithms/proofs/ahof/greedy_policy.clj) | AHoF greedy policy extraction: given a state-action value function Q(s, .), the greedy policy chooses the action of maximal value, pi(s) = argmax_a Q(s, a), greedy-value(s) = max_a Q(s, a). |
| [`rainbow.algorithms.proofs.ahof.held-karp`](../src/rainbow/algorithms/proofs/ahof/held_karp.clj) | AHoF Held-Karp Algorithm: solve the Travelling Salesman Problem EXACTLY in O(2^n * n^2) -- exponential, but far better than the O(n!) brute force -- by dynamic programming over SUBSETS of visited cities. |
| [`rainbow.algorithms.proofs.ahof.hierarchical-clustering`](../src/rainbow/algorithms/proofs/ahof/hierarchical_clustering.clj) | AHoF Agglomerative Hierarchical Clustering: build a hierarchy of clusters (a dendrogram) bottom-up -- start with each point in its own cluster and repeatedly MERGE THE TWO CLOSEST clusters, under a linkage that defines i |
| [`rainbow.algorithms.proofs.ahof.hmc`](../src/rainbow/algorithms/proofs/ahof/hmc.clj) | AHoF V24 Hamiltonian Monte Carlo -- the leapfrog integrator that simulates Hamiltonian dynamics to make distant, high-acceptance proposals. |
| [`rainbow.algorithms.proofs.ahof.hmm-forward`](../src/rainbow/algorithms/proofs/ahof/hmm_forward.clj) | AHoF HMM Forward Algorithm: compute the TOTAL likelihood of an observation sequence under a Hidden Markov Model by summing over all hidden-state paths -- the sum-product companion to Viterbi's max-product decoding. |
| [`rainbow.algorithms.proofs.ahof.hsvi`](../src/rainbow/algorithms/proofs/ahof/hsvi.clj) | AHoF D73 HSVI (Heuristic Search Value Iteration for POMDPs): maintain an upper and a lower bound on the optimal value function and search belief points to tighten them; the algorithm has converged at a belief when the bo |
| [`rainbow.algorithms.proofs.ahof.huffman`](../src/rainbow/algorithms/proofs/ahof/huffman.clj) | AHoF Huffman Coding: build an optimal prefix-free binary code by a greedy bottom-up merge. |
| [`rainbow.algorithms.proofs.ahof.hungarian`](../src/rainbow/algorithms/proofs/ahof/hungarian.clj) | AHoF Hungarian Algorithm (Kuhn-Munkres): find a minimum-cost perfect assignment of n agents to n tasks in O(n^3) -- the exact solver for the assignment problem (job scheduling, tracking, matching). |
| [`rainbow.algorithms.proofs.ahof.hypergradient-hg`](../src/rainbow/algorithms/proofs/ahof/hypergradient_hg.clj) | AHoF O25 Hypergradient Descent: adapt the learning rate online by a hypergradient\n correction, updating rate-update rate adjustment = rate + adjustment. |
| [`rainbow.algorithms.proofs.ahof.hypothesis-test`](../src/rainbow/algorithms/proofs/ahof/hypothesis_test.clj) | AHoF Statistical Hypothesis Testing (z-test / critical-value decision): decide whether observed data are inconsistent with a null hypothesis at a chosen significance level. |
| [`rainbow.algorithms.proofs.ahof.imitation-irl`](../src/rainbow/algorithms/proofs/ahof/imitation_irl.clj) | Kochenderfer imitation-learning / inverse-RL / structure-learning cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: D18.3 SMILe : stochastic mixture of expert-imitating polic |
| [`rainbow.algorithms.proofs.ahof.importance-sampling`](../src/rainbow/algorithms/proofs/ahof/importance_sampling.clj) | AHoF D7 worked likelihood-weighted (importance) sampling over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.interval-arithmetic`](../src/rainbow/algorithms/proofs/ahof/interval_arithmetic.clj) | AHoF V40 worked interval arithmetic over exact rationals on the interval [1/2, 3/2]. |
| [`rainbow.algorithms.proofs.ahof.is-falsification`](../src/rainbow/algorithms/proofs/ahof/is_falsification.clj) | AHoF V27 Importance Sampling: estimate the probability of a rare failure event by sampling from a proposal distribution and reweighting by the importance weight, the ratio of the target density to the proposal density: i |
| [`rainbow.algorithms.proofs.ahof.isotropic-es`](../src/rainbow/algorithms/proofs/ahof/isotropic_es.clj) | AHoF D44 Isotropic Evolutionary Strategies: perturb with isotropic Gaussian noise and keep the fitter offspring; between two fitnesses it keeps the larger value: prefers-fitter? |
| [`rainbow.algorithms.proofs.ahof.ista`](../src/rainbow/algorithms/proofs/ahof/ista.clj) | AHoF O-family ISTA (Iterative Shrinkage-Thresholding / proximal gradient): the standard first-order method for L1-regularized (LASSO) problems. |
| [`rainbow.algorithms.proofs.ahof.jaccard-similarity`](../src/rainbow/algorithms/proofs/ahof/jaccard_similarity.clj) | AHoF Jaccard Similarity: measure how alike two SETS are by the size of their intersection over the size of their union, jaccard intersection-size union-size = \|A intersect B\| / \|A union B\|, a value in [0, 1] that is 1 fo |
| [`rainbow.algorithms.proofs.ahof.johnson`](../src/rainbow/algorithms/proofs/ahof/johnson.clj) | AHoF Johnson's Algorithm (all-pairs shortest paths): compute shortest paths between EVERY pair of vertices in a sparse, possibly negative-weight (but cycle-free) graph in O(V*E + V^2 log V) -- faster than Floyd-Warshall  |
| [`rainbow.algorithms.proofs.ahof.k2`](../src/rainbow/algorithms/proofs/ahof/k2.clj) | AHoF D15 K2 Graph Search: greedy Bayesian-network structure learning. |
| [`rainbow.algorithms.proofs.ahof.kadane`](../src/rainbow/algorithms/proofs/ahof/kadane.clj) | AHoF Kadane's Algorithm: find the maximum-sum contiguous subarray in a single O(n) pass. |
| [`rainbow.algorithms.proofs.ahof.kalman`](../src/rainbow/algorithms/proofs/ahof/kalman.clj) | AHoF D-family Kalman Filter: the optimal linear estimator for a Gaussian-linear system, alternating a predict step (propagate mean and variance) and an update step that fuses a noisy measurement. |
| [`rainbow.algorithms.proofs.ahof.karger`](../src/rainbow/algorithms/proofs/ahof/karger.clj) | AHoF Karger's Min-Cut Algorithm (randomized): estimate the minimum cut of an undirected graph -- the fewest edges whose removal disconnects it -- by repeatedly CONTRACTING a uniformly random edge (merging its endpoints,  |
| [`rainbow.algorithms.proofs.ahof.kde`](../src/rainbow/algorithms/proofs/ahof/kde.clj) | AHoF D12 Nonparametric Learning (Kernel Density Estimation): estimate a density as a sum of kernels centered at the data points, each with bandwidth h. |
| [`rainbow.algorithms.proofs.ahof.kernel-smoothing`](../src/rainbow/algorithms/proofs/ahof/kernel_smoothing.clj) | AHoF D26 Kernel Smoothing value-function approximation: approximate the value at a query state by a kernel-weighted average of the stored sample values, with weights given by a similarity kernel. |
| [`rainbow.algorithms.proofs.ahof.kkt`](../src/rainbow/algorithms/proofs/ahof/kkt.clj) | AHoF O53 Lagrange Multipliers (KKT): the stationarity condition of the Karush-Kuhn-Tucker system. |
| [`rainbow.algorithms.proofs.ahof.kmeans`](../src/rainbow/algorithms/proofs/ahof/kmeans.clj) | AHoF K-Means Clustering (Lloyd's algorithm): partition points into k clusters by alternating an ASSIGNMENT step (assign each point to the nearest cluster centroid) and an UPDATE step (move each centroid to the mean of it |
| [`rainbow.algorithms.proofs.ahof.kmp`](../src/rainbow/algorithms/proofs/ahof/kmp.clj) | AHoF Knuth-Morris-Pratt (KMP) string matching: find all occurrences of a pattern in a text in O(n + m) time -- never re-examining a text character -- by precomputing a FAILURE FUNCTION that says, on a mismatch after matc |
| [`rainbow.algorithms.proofs.ahof.knapsack`](../src/rainbow/algorithms/proofs/ahof/knapsack.clj) | AHoF 0/1 Knapsack (dynamic programming): choose a subset of items maximizing total value under a weight capacity. |
| [`rainbow.algorithms.proofs.ahof.knn`](../src/rainbow/algorithms/proofs/ahof/knn.clj) | AHoF K-Nearest Neighbors (instance-based classification): classify a query point by a majority vote among its K nearest training examples -- a non-parametric method with no training phase (lazy learning). |
| [`rainbow.algorithms.proofs.ahof.kosaraju`](../src/rainbow/algorithms/proofs/ahof/kosaraju.clj) | AHoF Kosaraju's Algorithm: find the strongly connected components (SCCs) of a directed graph in O(V + E) via two depth-first passes -- one on the graph (recording finish order) and one on the TRANSPOSE (grouping by reach |
| [`rainbow.algorithms.proofs.ahof.kruskal`](../src/rainbow/algorithms/proofs/ahof/kruskal.clj) | AHoF Kruskal's Minimum Spanning Tree: build an MST by scanning edges in increasing weight order and adding each edge unless it would form a cycle -- i.e. |
| [`rainbow.algorithms.proofs.ahof.lao-star`](../src/rainbow/algorithms/proofs/ahof/lao_star.clj) | AHoF D38 Labeled Heuristic Search (LAO*): expand the best (lowest f-cost) node on the frontier of the explicit AND/OR graph; between two f-costs it keeps the smaller value: prefers-lower-f? |
| [`rainbow.algorithms.proofs.ahof.lbfgs`](../src/rainbow/algorithms/proofs/ahof/lbfgs.clj) | AHoF O30 L-BFGS: limited-memory BFGS storing recent (s, y) pairs; the stored gradient\n change is y = g_{k+1} - g_k: gradient-change g-new g-old = g-new - g-old. |
| [`rainbow.algorithms.proofs.ahof.lcs`](../src/rainbow/algorithms/proofs/ahof/lcs.clj) | AHoF Longest Common Subsequence (dynamic programming): the length of the longest subsequence common to two sequences -- the basis of diff, version control merges, and bioinformatics alignment. |
| [`rainbow.algorithms.proofs.ahof.levenberg-marquardt`](../src/rainbow/algorithms/proofs/ahof/levenberg_marquardt.clj) | AHoF O31 worked Levenberg-Marquardt: the general descent skeleton with a damped Hessian-inverse step size, on the quadratic f(x) = x^2. |
| [`rainbow.algorithms.proofs.ahof.linear-interpolation`](../src/rainbow/algorithms/proofs/ahof/linear_interpolation.clj) | AHoF D27 Linear Interpolation over exact rationals: interpolate between two values a and b with convex weights w0, w1 (summing to one), lerp a b w0 w1 = w0 * a + w1 * b. |
| [`rainbow.algorithms.proofs.ahof.linear-regression-vf`](../src/rainbow/algorithms/proofs/ahof/linear_regression_vf.clj) | AHoF D29 Linear Regression Value Function: approximate the value function as a linear combination of state features, V(s) = w . |
| [`rainbow.algorithms.proofs.ahof.lis`](../src/rainbow/algorithms/proofs/ahof/lis.clj) | AHoF Longest Increasing Subsequence (LIS): find the length of the longest strictly-increasing subsequence of a sequence -- underlying diff/patience sorting, box-stacking, and scheduling. |
| [`rainbow.algorithms.proofs.ahof.local-policy-search`](../src/rainbow/algorithms/proofs/ahof/local_policy_search.clj) | AHoF D40 Local Policy Search: hill climbing in policy-parameter space. |
| [`rainbow.algorithms.proofs.ahof.local-search`](../src/rainbow/algorithms/proofs/ahof/local_search.clj) | AHoF D40 worked bounded local (hill-climbing) policy search. |
| [`rainbow.algorithms.proofs.ahof.log-loss`](../src/rainbow/algorithms/proofs/ahof/log_loss.clj) | AHoF Cross-Entropy / Log Loss: the standard loss for probabilistic classification and the maximum-likelihood objective for logistic regression and softmax networks. |
| [`rainbow.algorithms.proofs.ahof.logistic-regression`](../src/rainbow/algorithms/proofs/ahof/logistic_regression.clj) | AHoF Logistic Regression: a probabilistic linear classifier that models the class probability as the logistic sigmoid of a linear score, P(y=1\|x) = sigmoid(w.x + b), trained by maximizing the log-likelihood (gradient asc |
| [`rainbow.algorithms.proofs.ahof.lp-mdp`](../src/rainbow/algorithms/proofs/ahof/lp_mdp.clj) | AHoF D24 LP Formulation of an MDP: the optimal value function is the solution of a linear program that minimizes the total value subject to the Bellman inequality constraints -- for every state-action pair the value must |
| [`rainbow.algorithms.proofs.ahof.lp-reachability`](../src/rainbow/algorithms/proofs/ahof/lp_reachability.clj) | AHoF V39 LP-Based Reachability: compute reachable-set bounds by solving linear programs; a candidate is reachable within a facet when the LP objective value stays within the facet bound: lp-reachable? |
| [`rainbow.algorithms.proofs.ahof.lqr`](../src/rainbow/algorithms/proofs/ahof/lqr.clj) | LQR linear feedback control (Kochenderfer Decision Making D7.11), one of the signed-subtraction cluster deferred in August until the signed layer landed. |
| [`rainbow.algorithms.proofs.ahof.ltl-model-checking`](../src/rainbow/algorithms/proofs/ahof/ltl_model_checking.clj) | AHoF V7 LTL Model Checking: check a Linear Temporal Logic specification against a system; quantitatively the spec is satisfied when the trace robustness meets the required margin: satisfied? |
| [`rainbow.algorithms.proofs.ahof.manacher`](../src/rainbow/algorithms/proofs/ahof/manacher.clj) | AHoF Manacher's Algorithm: find the longest palindromic substring (and all maximal palindrome radii) in LINEAR time, beating the O(n^2) expand-around-center approach by reusing mirror symmetry so each position is examine |
| [`rainbow.algorithms.proofs.ahof.matrix-chain`](../src/rainbow/algorithms/proofs/ahof/matrix_chain.clj) | AHoF Matrix Chain Multiplication (dynamic programming): find the parenthesization of a chain of matrix products that minimizes the number of scalar multiplications. |
| [`rainbow.algorithms.proofs.ahof.maximum-likelihood`](../src/rainbow/algorithms/proofs/ahof/maximum_likelihood.clj) | AHoF D10 worked maximum likelihood estimation over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.mc-dropout`](../src/rainbow/algorithms/proofs/ahof/mc_dropout.clj) | AHoF V62 MC Dropout Uncertainty: estimate predictive uncertainty from the variance of stochastic-dropout forward passes and flag an input uncertain when that variance reaches the threshold: uncertain? |
| [`rainbow.algorithms.proofs.ahof.mc-mean`](../src/rainbow/algorithms/proofs/ahof/mc_mean.clj) | AHoF O69 Uncertainty Propagation (Monte Carlo): propagate input uncertainty by sampling and averaging the outputs. |
| [`rainbow.algorithms.proofs.ahof.mcts`](../src/rainbow/algorithms/proofs/ahof/mcts.clj) | AHoF D36 Monte Carlo Tree Search: incrementally grow a search tree by selection, expansion, simulation, and backpropagation. |
| [`rainbow.algorithms.proofs.ahof.mcts-falsification`](../src/rainbow/algorithms/proofs/ahof/mcts_falsification.clj) | AHoF V19 MCTS for Falsification: Monte Carlo tree search over the space of system behaviours to find a specification violation, selecting child nodes by their UCB score and keeping the higher-scoring child: prefers-child |
| [`rainbow.algorithms.proofs.ahof.mean-value-inclusion`](../src/rainbow/algorithms/proofs/ahof/mean_value_inclusion.clj) | AHoF V42 Mean-Value Inclusion: a tighter interval extension than the natural inclusion, using the mean-value form to enclose a function's range in [lo, hi]; a value is certified within the enclosure when it lies between  |
| [`rainbow.algorithms.proofs.ahof.merge-sort`](../src/rainbow/algorithms/proofs/ahof/merge_sort.clj) | AHoF Merge Sort: a stable, worst-case O(n log n) comparison sort by divide-and-conquer -- split the list in half, recursively sort each half, then MERGE the two sorted halves. |
| [`rainbow.algorithms.proofs.ahof.mesh-adaptive`](../src/rainbow/algorithms/proofs/ahof/mesh_adaptive.clj) | AHoF O39 Mesh Adaptive Direct Search (MADS): a derivative-free direct-search method that probes the objective at mesh points around the incumbent. |
| [`rainbow.algorithms.proofs.ahof.min-max-scaling`](../src/rainbow/algorithms/proofs/ahof/min_max_scaling.clj) | AHoF Min-Max Scaling (normalization): rescale a feature linearly to the unit interval [0, 1] by mapping the minimum to 0 and the maximum to 1, scaled offset range = (x - min) / (max - min), where offset = x - min and ran |
| [`rainbow.algorithms.proofs.ahof.mle-system`](../src/rainbow/algorithms/proofs/ahof/mle_system.clj) | AHoF V1 MLE for System Models: fit a system model by maximum likelihood, keeping the model with the larger data likelihood: prefers-model-zero? |
| [`rainbow.algorithms.proofs.ahof.momentum`](../src/rainbow/algorithms/proofs/ahof/momentum.clj) | AHoF O19 worked Polyak momentum over signed rationals with pair state. |
| [`rainbow.algorithms.proofs.ahof.monte-carlo`](../src/rainbow/algorithms/proofs/ahof/monte_carlo.clj) | AHoF V26 worked direct Monte Carlo failure-probability estimation. |
| [`rainbow.algorithms.proofs.ahof.mse`](../src/rainbow/algorithms/proofs/ahof/mse.clj) | AHoF Mean Squared Error: the standard loss for regression and the objective of least-squares fitting -- the average of the squared prediction errors, squared-error e = e * e mse e0 e1 = (e0*e0 + e1*e1) / 2 (a two-sample  |
| [`rainbow.algorithms.proofs.ahof.multilevel-splitting`](../src/rainbow/algorithms/proofs/ahof/multilevel_splitting.clj) | AHoF V32 Multilevel Splitting: estimate rare-event probability by splitting particles that cross intermediate levels toward the rare set; a particle reaches a level when its score meets that level: reaches-level? |
| [`rainbow.algorithms.proofs.ahof.multiobjective`](../src/rainbow/algorithms/proofs/ahof/multiobjective.clj) | Kochenderfer 'Algorithms for Optimization' Ch.15-16 multiobjective / sampling-plan selection rules as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: O15.3 non-dominated sorting : a |
| [`rainbow.algorithms.proofs.ahof.mutation-testing`](../src/rainbow/algorithms/proofs/ahof/mutation_testing.clj) | AHoF V-family Mutation Testing: assess a test suite's fault-detection power by seeding many small program mutants and measuring how many the suite KILLS (detects). |
| [`rainbow.algorithms.proofs.ahof.n-queens`](../src/rainbow/algorithms/proofs/ahof/n_queens.clj) | AHoF N-Queens (backtracking constraint satisfaction): place N queens on an NxN board so none attacks another -- the textbook example of backtracking search, which extends a partial placement column by column and abandons |
| [`rainbow.algorithms.proofs.ahof.naive-bayes`](../src/rainbow/algorithms/proofs/ahof/naive_bayes.clj) | AHoF D-family Naive Bayes classifier: predict a class from features assumed conditionally independent given the class. |
| [`rainbow.algorithms.proofs.ahof.nash-equilibrium`](../src/rainbow/algorithms/proofs/ahof/nash_equilibrium.clj) | AHoF D77 Nash Equilibrium (support enumeration): a strategy profile is a Nash equilibrium when no player can gain by unilaterally deviating. |
| [`rainbow.algorithms.proofs.ahof.nash-q-learning`](../src/rainbow/algorithms/proofs/ahof/nash_q_learning.clj) | AHoF D81 Nash Q-Learning (classical: learn stage-game Q-values and back up the Nash EQUILIBRIUM value of each stage game, Hu-Wellman 2003). |
| [`rainbow.algorithms.proofs.ahof.natural-gradient`](../src/rainbow/algorithms/proofs/ahof/natural_gradient.clj) | AHoF D50 Natural Gradient: the policy update that ascends along the natural gradient -- the ordinary gradient preconditioned by the inverse Fisher information matrix, so the step is invariant to the parameterization of t |
| [`rainbow.algorithms.proofs.ahof.natural-gradient-ng`](../src/rainbow/algorithms/proofs/ahof/natural_gradient_ng.clj) | AHoF D50 Natural Gradient: precondition the gradient by the inverse Fisher metric and\n step; the parameter update descends update theta step = theta - step. |
| [`rainbow.algorithms.proofs.ahof.natural-inclusion`](../src/rainbow/algorithms/proofs/ahof/natural_inclusion.clj) | AHoF V41 Natural Inclusion Function: replace each variable in an expression by its interval and evaluate with interval arithmetic to get a guaranteed enclosure [lo, hi] of the range; the true range is contained, so a can |
| [`rainbow.algorithms.proofs.ahof.nearest-neighbor`](../src/rainbow/algorithms/proofs/ahof/nearest_neighbor.clj) | AHoF D25 worked nearest-neighbor value function approximation over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.nesterov`](../src/rainbow/algorithms/proofs/ahof/nesterov.clj) | AHoF O20 worked Nesterov accelerated momentum over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.network-scoring`](../src/rainbow/algorithms/proofs/ahof/network_scoring.clj) | AHoF D14 worked additive Bayesian-network scoring. |
| [`rainbow.algorithms.proofs.ahof.neural-vf`](../src/rainbow/algorithms/proofs/ahof/neural_vf.clj) | AHoF D30 Neural Network Value Function: approximate the value function with a trainable neural network. |
| [`rainbow.algorithms.proofs.ahof.newton`](../src/rainbow/algorithms/proofs/ahof/newton.clj) | AHoF O26 worked Newton's method: the general descent skeleton with a Hessian-inverse step size, on the quadratic f(x) = x^2. |
| [`rainbow.algorithms.proofs.ahof.nn-verification`](../src/rainbow/algorithms/proofs/ahof/nn_verification.clj) | AHoF V47 Neural Network Verification: certify that a network's output stays within a safety bound over an input region; a concrete output is safe when it is within the safety bound: safe? |
| [`rainbow.algorithms.proofs.ahof.nnls`](../src/rainbow/algorithms/proofs/ahof/nnls.clj) | Nonnegative projection for NNLS (Kochenderfer Optimization O13.4), a signed-cluster algorithm deferred in August: over nonnegative rationals the projection is degenerate, so it needed the signed layer's max(x,0). |
| [`rainbow.algorithms.proofs.ahof.o72-branch-and-bound`](../src/rainbow/algorithms/proofs/ahof/o72_branch_and_bound.clj) | AHoF O72 Branch and Bound (optimization form) worked pruning step over exact rationals, reusing the shared bounding lemma (rainbow.algorithms.proofs.branch-and-bound). |
| [`rainbow.algorithms.proofs.ahof.odd-monitor`](../src/rainbow/algorithms/proofs/ahof/odd_monitor.clj) | AHoF V59 worked ODD monitor over the 2-D operating envelope [0,1] x [0,2]. |
| [`rainbow.algorithms.proofs.ahof.ols-regression`](../src/rainbow/algorithms/proofs/ahof/ols_regression.clj) | AHoF Ordinary Least Squares (simple linear regression): fit a line y = slope*x + intercept minimizing the sum of squared residuals. |
| [`rainbow.algorithms.proofs.ahof.open-loop-planning`](../src/rainbow/algorithms/proofs/ahof/open_loop_planning.clj) | AHoF D39 Open-Loop Planning: optimize a fixed open-loop action sequence, keeping the plan with the larger total value; it keeps the larger value: prefers-plan-zero? |
| [`rainbow.algorithms.proofs.ahof.opt-reachability`](../src/rainbow/algorithms/proofs/ahof/opt_reachability.clj) | AHoF V45 Optimization-Based Reach: bound the reachable set by solving an optimization in each direction; a direction's reach is certified when the optimal reach value stays within the bound: reach-bounded? |
| [`rainbow.algorithms.proofs.ahof.order-reduction`](../src/rainbow/algorithms/proofs/ahof/order_reduction.clj) | AHoF V38 Order Reduction: reduce the generator/complexity order of a set representation while over-approximating; the reduction is sound when the incurred over-approximation error stays within the tolerance: reduction-so |
| [`rainbow.algorithms.proofs.ahof.pagerank`](../src/rainbow/algorithms/proofs/ahof/pagerank.clj) | AHoF PageRank: rank the nodes of a directed graph by importance -- the stationary distribution of a random surfer who follows out-links with probability d (the damping factor) and teleports to a uniformly random node wit |
| [`rainbow.algorithms.proofs.ahof.pareto`](../src/rainbow/algorithms/proofs/ahof/pareto.clj) | AHoF multiobjective optimization -- Pareto dominance, the partial order that defines the Pareto front. |
| [`rainbow.algorithms.proofs.ahof.particle-filter`](../src/rainbow/algorithms/proofs/ahof/particle_filter.clj) | AHoF D10 Particle Filter (sequential Monte Carlo): approximate a filtering distribution by a weighted set of particles, propagated and reweighted each step, then RESAMPLED to combat weight degeneracy. |
| [`rainbow.algorithms.proofs.ahof.particle-filter-pf`](../src/rainbow/algorithms/proofs/ahof/particle_filter_pf.clj) | AHoF D70 Particle Filter: approximate the posterior by a weighted particle set; the\n state estimate is the weighted mean estimate w0 x0 w1 x1 = w0*x0 + w1*x1. |
| [`rainbow.algorithms.proofs.ahof.partitioning`](../src/rainbow/algorithms/proofs/ahof/partitioning.clj) | AHoF V46 Partitioning: recursively split the state/input set into cells so each is small enough for an accurate local over-approximation; a cell is fine enough when its diameter is within the tolerance: fine-enough? |
| [`rainbow.algorithms.proofs.ahof.pattern-search`](../src/rainbow/algorithms/proofs/ahof/pattern_search.clj) | AHoF O35 worked generalized pattern search over exact rationals, minimizing f(x) = x^2 from x = 2 with step 1. |
| [`rainbow.algorithms.proofs.ahof.pbvi`](../src/rainbow/algorithms/proofs/ahof/pbvi.clj) | AHoF D72 PBVI (Point-Based Value Iteration for POMDPs): maintain value at a finite set of belief points, backing up each point's value as the maximum over candidate alpha vectors of the value at that belief. |
| [`rainbow.algorithms.proofs.ahof.pc`](../src/rainbow/algorithms/proofs/ahof/pc.clj) | AHoF D16 PC Algorithm: constraint-based Bayesian-network structure learning. |
| [`rainbow.algorithms.proofs.ahof.penalty`](../src/rainbow/algorithms/proofs/ahof/penalty.clj) | AHoF O-family Penalty Method: solve a constrained optimization problem by a sequence of UNCONSTRAINED problems whose objective adds a penalty proportional to the constraint violation, penalized f mu violation = f + mu *  |
| [`rainbow.algorithms.proofs.ahof.perceptron`](../src/rainbow/algorithms/proofs/ahof/perceptron.clj) | AHoF Perceptron (Rosenblatt): the foundational linear classifier and the atom of neural networks. |
| [`rainbow.algorithms.proofs.ahof.policy-evaluation`](../src/rainbow/algorithms/proofs/ahof/policy_evaluation.clj) | AHoF D20 specialization of bounded exact-rational policy evaluation. |
| [`rainbow.algorithms.proofs.ahof.policy-evaluation-backup`](../src/rainbow/algorithms/proofs/ahof/policy_evaluation_backup.clj) | AHoF D-family Policy Evaluation: the evaluation half of policy iteration. |
| [`rainbow.algorithms.proofs.ahof.policy-gradient`](../src/rainbow/algorithms/proofs/ahof/policy_gradient.clj) | AHoF D49 Gradient Ascent Update (policy gradient): the parameter update at the heart of policy-gradient reinforcement learning. |
| [`rainbow.algorithms.proofs.ahof.policy-iteration`](../src/rainbow/algorithms/proofs/ahof/policy_iteration.clj) | AHoF D21 worked bounded policy-iteration step. |
| [`rainbow.algorithms.proofs.ahof.policy-visualization`](../src/rainbow/algorithms/proofs/ahof/policy_visualization.clj) | AHoF V53 Policy Visualization: render a learned policy by displaying, at each state, the greedy action -- the one with the maximal action value. |
| [`rainbow.algorithms.proofs.ahof.polytope`](../src/rainbow/algorithms/proofs/ahof/polytope.clj) | AHoF V34 Polytope Propagation: represent a reachable set as an intersection of halfspaces (a polytope) and propagate it forward. |
| [`rainbow.algorithms.proofs.ahof.pomcp`](../src/rainbow/algorithms/proofs/ahof/pomcp.clj) | AHoF D75 Online POMDP (POMCP): Monte Carlo tree search in belief space, selecting actions at each node by their UCB score and keeping the higher-scoring action. |
| [`rainbow.algorithms.proofs.ahof.pomdp-bounds`](../src/rainbow/algorithms/proofs/ahof/pomdp_bounds.clj) | Kochenderfer 'Algorithms for Decision Making' Ch.21 offline POMDP value-function bounds, expressed as higher-order-function compositions over belief-weighted alpha-vector values and proved axiom-free, extending the 222 A |
| [`rainbow.algorithms.proofs.ahof.pomdp-online`](../src/rainbow/algorithms/proofs/ahof/pomdp_online.clj) | Kochenderfer 'Algorithms for Decision Making' Ch.21-23 online / point-based / controller POMDP cores as higher-order-function compositions, proved axiom-free (each with its most distinctive structural property), extendin |
| [`rainbow.algorithms.proofs.ahof.ppo`](../src/rainbow/algorithms/proofs/ahof/ppo.clj) | AHoF D43 Proximal Policy Optimization: a policy-gradient method that keeps updates in a trust region by CLIPPING the probability ratio r = pi_new/pi_old into [1 - eps, 1 + eps] before forming the surrogate objective. |
| [`rainbow.algorithms.proofs.ahof.precision-recall`](../src/rainbow/algorithms/proofs/ahof/precision_recall.clj) | AHoF Precision and Recall: the two complementary quality metrics of a binary classifier, computed from the confusion-matrix counts (true/false positives and negatives), precision tp fp = tp / (tp + fp) (of predicted posi |
| [`rainbow.algorithms.proofs.ahof.prim`](../src/rainbow/algorithms/proofs/ahof/prim.clj) | AHoF Prim's Minimum Spanning Tree: grow an MST from a start vertex by repeatedly adding the minimum-weight edge that CROSSES THE CUT between the in-tree vertices and the rest. |
| [`rainbow.algorithms.proofs.ahof.prob-programming`](../src/rainbow/algorithms/proofs/ahof/prob_programming.clj) | AHoF V25 Probabilistic Programming: an observe/factor statement reweights the trace\n by the observation likelihood; the trace score combines two factors multiplicatively\n score a b = a * b. |
| [`rainbow.algorithms.proofs.ahof.prob-robust`](../src/rainbow/algorithms/proofs/ahof/prob_robust.clj) | AHoF O75 Probabilistic Robust Optimization: satisfy constraints with high probability under uncertainty; a design is chance-feasible when its violation probability is within the risk level alpha: chance-feasible? |
| [`rainbow.algorithms.proofs.ahof.probabilistic-reachability`](../src/rainbow/algorithms/proofs/ahof/probabilistic_reachability.clj) | AHoF V51 Probabilistic Reachability: compute the probability of reaching a target set and flag it likely-reachable when that probability meets a confidence threshold: likely-reachable? |
| [`rainbow.algorithms.proofs.ahof.projection-methods`](../src/rainbow/algorithms/proofs/ahof/projection_methods.clj) | Kochenderfer constrained/rounded update rules as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: O10.1 projected gradient descent : project the updated point onto a box [lo,hi] D12. |
| [`rainbow.algorithms.proofs.ahof.q-learning`](../src/rainbow/algorithms/proofs/ahof/q_learning.clj) | AHoF D61 worked temporal-difference (Q-learning) update over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.qmdp`](../src/rainbow/algorithms/proofs/ahof/qmdp.clj) | AHoF D22 QMDP (POMDP planning approximation): approximate the value of an action under partial observability by weighting the fully-observable Q-values by the current belief over states, qmdp-value b0 q0 b1 q1 = b0 * Q(s |
| [`rainbow.algorithms.proofs.ahof.qp`](../src/rainbow/algorithms/proofs/ahof/qp.clj) | AHoF O56 Quadratic Programming: minimize a convex quadratic objective subject to linear constraints, typically by encoding the KKT stationarity system. |
| [`rainbow.algorithms.proofs.ahof.quadratic-fit`](../src/rainbow/algorithms/proofs/ahof/quadratic_fit.clj) | AHoF O10 Quadratic Fit Search: fit a parabola through three sampled points and step toward its vertex, keeping the three lowest-valued points as the bracket shrinks. |
| [`rainbow.algorithms.proofs.ahof.quickselect`](../src/rainbow/algorithms/proofs/ahof/quickselect.clj) | AHoF Quickselect (Hoare's selection): find the k-th smallest element of an unsorted array in expected O(n) -- faster than sorting -- by partitioning around a pivot (as in quicksort) but recursing into ONLY the side that  |
| [`rainbow.algorithms.proofs.ahof.quicksort`](../src/rainbow/algorithms/proofs/ahof/quicksort.clj) | AHoF Quicksort: an in-place, average-case O(n log n) comparison sort by divide-and-conquer -- pick a pivot, PARTITION the remaining elements into those at most the pivot and those greater, then recursively sort each side |
| [`rainbow.algorithms.proofs.ahof.r-squared`](../src/rainbow/algorithms/proofs/ahof/r_squared.clj) | AHoF R-squared (coefficient of determination): summarize how well a regression fits by the FRACTION of the total variance in the target that the model explains, r-squared explained-variance total-variance = explained-var |
| [`rainbow.algorithms.proofs.ahof.rabin-karp`](../src/rainbow/algorithms/proofs/ahof/rabin_karp.clj) | AHoF Rabin-Karp string matching: find a pattern in a text in expected O(n+m) by comparing a ROLLING HASH of each text window against the pattern's hash -- updating the window hash in O(1) as it slides (remove the leaving |
| [`rainbow.algorithms.proofs.ahof.radix-sort`](../src/rainbow/algorithms/proofs/ahof/radix_sort.clj) | AHoF Radix Sort (LSD): sort fixed-width integer keys in O(n * d) without comparing whole keys -- process the digits from LEAST to most significant, and on each pass STABLY sort by that digit only. |
| [`rainbow.algorithms.proofs.ahof.ratio-normalizing`](../src/rainbow/algorithms/proofs/ahof/ratio_normalizing.clj) | AHoF V31 Ratio of Normalizing Constants: estimate the ratio of two normalizing constants (partition functions) Z1/Z2, the quantity underlying Bayes factors and bridge/path sampling: ratio z1 z2 = z1 / z2. |
| [`rainbow.algorithms.proofs.ahof.rbf-surrogate`](../src/rainbow/algorithms/proofs/ahof/rbf_surrogate.clj) | AHoF O61 Radial Basis Function surrogate: an interpolating surrogate model that predicts by a weighted sum of radial basis functions centered at the sampled points. |
| [`rainbow.algorithms.proofs.ahof.reachability-eda`](../src/rainbow/algorithms/proofs/ahof/reachability_eda.clj) | Final Kochenderfer straggler cores (reachability, robustness envelope, adaptive SA, estimation-of-distribution program search) as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: V10 |
| [`rainbow.algorithms.proofs.ahof.reachability-spec`](../src/rainbow/algorithms/proofs/ahof/reachability_spec.clj) | AHoF V8 Reachability Specification: a reachability property asks whether the system can reach a target set; concretely a trajectory reaches the target when its distance to the target set falls within the specification to |
| [`rainbow.algorithms.proofs.ahof.receding-horizon`](../src/rainbow/algorithms/proofs/ahof/receding_horizon.clj) | AHoF D31 Receding Horizon Control (model-predictive control): rather than commit to a whole open-loop plan, the controller solves the finite-horizon problem, applies only the FIRST action of the resulting plan, then re-s |
| [`rainbow.algorithms.proofs.ahof.regression-gradient`](../src/rainbow/algorithms/proofs/ahof/regression_gradient.clj) | AHoF O6 Regression Gradient: the least-squares gradient is driven by the residual\n actual - predicted, which the gradient sums over data: residual actual predicted =\n actual - predicted. |
| [`rainbow.algorithms.proofs.ahof.reinforce`](../src/rainbow/algorithms/proofs/ahof/reinforce.clj) | AHoF D46 REINFORCE (likelihood-ratio policy gradient): the Monte-Carlo policy gradient estimator weights each sampled trajectory's score-function by its return. |
| [`rainbow.algorithms.proofs.ahof.rejection`](../src/rainbow/algorithms/proofs/ahof/rejection.clj) | AHoF D6 Rejection Sampling: draw a proposal and a uniform u, accepting the proposal when u falls under the acceptance ratio f(x)/(M g(x)): accepts? |
| [`rainbow.algorithms.proofs.ahof.rejection-sampling`](../src/rainbow/algorithms/proofs/ahof/rejection_sampling.clj) | AHoF V21 Rejection Sampling (for failure events): draw samples and keep only those consistent with the evidence / that hit the target event, rejecting the rest. |
| [`rainbow.algorithms.proofs.ahof.reliability`](../src/rainbow/algorithms/proofs/ahof/reliability.clj) | AHoF V-family Series-System Reliability (reliability block diagram): a series system works only if EVERY component works, so with independent components its reliability is the product of the component reliabilities, seri |
| [`rainbow.algorithms.proofs.ahof.reservoir-sampling`](../src/rainbow/algorithms/proofs/ahof/reservoir_sampling.clj) | AHoF Reservoir Sampling (Algorithm R): draw a uniform random sample of fixed size k from a STREAM of unknown, possibly huge length in a SINGLE PASS and O(k) memory -- used for log sampling, streaming analytics, and datas |
| [`rainbow.algorithms.proofs.ahof.reverse-mode-ad`](../src/rainbow/algorithms/proofs/ahof/reverse_mode_ad.clj) | AHoF O5 Reverse-Mode Auto-Diff: backpropagate adjoints, accumulating each node's\n adjoint as the sum of its downstream contributions: adjoint-accumulate a b = a + b.\n Worked: 1+2=3. |
| [`rainbow.algorithms.proofs.ahof.rl-falsification`](../src/rainbow/algorithms/proofs/ahof/rl_falsification.clj) | AHoF V20 RL for Falsification: train an agent by reinforcement learning to drive the system toward a specification violation, acting greedily on the learned Q-values by keeping the higher-Q action: prefers-action-zero? |
| [`rainbow.algorithms.proofs.ahof.robust-optimization`](../src/rainbow/algorithms/proofs/ahof/robust_optimization.clj) | AHoF O74 Robust Optimization (set-based): optimize against the WORST case over an uncertainty set. |
| [`rainbow.algorithms.proofs.ahof.robustness-objective`](../src/rainbow/algorithms/proofs/ahof/robustness_objective.clj) | AHoF V13 worked robustness-based falsification objective over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.rod-cutting`](../src/rainbow/algorithms/proofs/ahof/rod_cutting.clj) | AHoF Rod Cutting (dynamic programming): given a rod of integer length and a price for each possible piece length, cut it into pieces maximizing total revenue. |
| [`rainbow.algorithms.proofs.ahof.rollout`](../src/rainbow/algorithms/proofs/ahof/rollout.clj) | AHoF D32 Rollout with Heuristic: estimate a state's value by simulating the rollout policy forward and averaging the returns. |
| [`rainbow.algorithms.proofs.ahof.roulette-selection`](../src/rainbow/algorithms/proofs/ahof/roulette_selection.clj) | AHoF genetic-algorithm operator: fitness-proportionate (roulette-wheel) selection. |
| [`rainbow.algorithms.proofs.ahof.sac`](../src/rainbow/algorithms/proofs/ahof/sac.clj) | AHoF D45 Soft Actor-Critic: an off-policy actor-critic that optimizes a MAXIMUM-ENTROPY objective, augmenting the reward with an entropy bonus so the policy stays as stochastic as possible while succeeding -- improving e |
| [`rainbow.algorithms.proofs.ahof.sarsa`](../src/rainbow/algorithms/proofs/ahof/sarsa.clj) | AHoF D62 worked SARSA on-policy update over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.sarsop`](../src/rainbow/algorithms/proofs/ahof/sarsop.clj) | AHoF D74 SARSOP (Successive Approximations of the Reachable Space under Optimal Policies): a point-based POMDP solver that samples beliefs reachable under the optimal policy and tightens value bounds; it has converged wh |
| [`rainbow.algorithms.proofs.ahof.sat`](../src/rainbow/algorithms/proofs/ahof/sat.clj) | AHoF V50 SAT-based Bounded Model Checking: the system is unrolled k steps and encoded as a boolean formula in CNF; a counterexample exists iff the formula is satisfiable. |
| [`rainbow.algorithms.proofs.ahof.secant`](../src/rainbow/algorithms/proofs/ahof/secant.clj) | AHoF O27 Secant Method: root-find by the secant update x - f(x)*(x-x_prev)/(f-f_prev);\n the divided-difference denominator is the value change value-change f-new f-old =\n f-new - f-old. |
| [`rainbow.algorithms.proofs.ahof.segment-tree`](../src/rainbow/algorithms/proofs/ahof/segment_tree.clj) | AHoF Segment Tree: answer range-aggregate queries (sum / min / max) AND point updates on an array, both in O(log n), by a balanced binary tree over array segments in which every internal node stores the aggregate of its  |
| [`rainbow.algorithms.proofs.ahof.sequential-decision`](../src/rainbow/algorithms/proofs/ahof/sequential_decision.clj) | Kochenderfer 'Algorithms for Decision Making' game-theory + model-based-RL cores as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: D24.8 iterated best response : best-response valu |
| [`rainbow.algorithms.proofs.ahof.set-cover`](../src/rainbow/algorithms/proofs/ahof/set_cover.clj) | AHoF Set Cover (greedy approximation): given a universe of elements and a collection of subsets, choose the fewest subsets whose union is the whole universe. |
| [`rainbow.algorithms.proofs.ahof.shap`](../src/rainbow/algorithms/proofs/ahof/shap.clj) | AHoF V55 SHAP Values: attribute a prediction to features as a weighted sum of feature\n contributions (Shapley-weighted); attribution w0 c0 w1 c1 = w0*c0 + w1*c1. |
| [`rainbow.algorithms.proofs.ahof.shooting`](../src/rainbow/algorithms/proofs/ahof/shooting.clj) | AHoF V16 Shooting Methods: trajectory-based trajectory optimization / open-loop control. |
| [`rainbow.algorithms.proofs.ahof.shubert`](../src/rainbow/algorithms/proofs/ahof/shubert.clj) | AHoF O11 Shubert-Piyavskii: build a piecewise-linear (sawtooth) lower bound of a Lipschitz objective and sample where the lower bound is smallest; between two candidate lower- bound values it keeps the smaller value: pre |
| [`rainbow.algorithms.proofs.ahof.simplex`](../src/rainbow/algorithms/proofs/ahof/simplex.clj) | AHoF O54 Simplex Algorithm -- the minimum-ratio test that chooses the leaving variable (pivot row) each iteration. |
| [`rainbow.algorithms.proofs.ahof.simplex-interpolation`](../src/rainbow/algorithms/proofs/ahof/simplex_interpolation.clj) | AHoF D28 Simplex Interpolation: interpolate a value function over a simplicial grid using barycentric coordinates. |
| [`rainbow.algorithms.proofs.ahof.simulated-annealing`](../src/rainbow/algorithms/proofs/ahof/simulated_annealing.clj) | AHoF Simulated Annealing: a global optimization metaheuristic that escapes local optima by sometimes accepting WORSE solutions -- with a probability that shrinks as a 'temperature' cools -- inspired by the annealing of m |
| [`rainbow.algorithms.proofs.ahof.sliding-window`](../src/rainbow/algorithms/proofs/ahof/sliding_window.clj) | AHoF Sliding Window: solve subarray/substring problems in one O(n) pass by maintaining a window that slides across the data, adding the entering element and removing the leaving one instead of recomputing over each subar |
| [`rainbow.algorithms.proofs.ahof.smc`](../src/rainbow/algorithms/proofs/ahof/smc.clj) | AHoF V30 Sequential Monte Carlo: propagate and resample a weighted particle set over time; the filtered estimate is the normalized weighted mean of the particles, estimate w0 x0 w1 x1 = w0*x0 + w1*x1. |
| [`rainbow.algorithms.proofs.ahof.sobol`](../src/rainbow/algorithms/proofs/ahof/sobol.clj) | AHoF O60 Sobol Sequences: a quasi-random low-discrepancy sequence for uniform space-filling sampling; the sequence meets its uniformity target when the star discrepancy stays within the bound: low-discrepancy? |
| [`rainbow.algorithms.proofs.ahof.softmax`](../src/rainbow/algorithms/proofs/ahof/softmax.clj) | AHoF Softmax: turn a vector of real-valued scores (logits) into a probability distribution over classes -- the standard output layer of multi-class classifiers and the policy head of policy-gradient RL. |
| [`rainbow.algorithms.proofs.ahof.spsa`](../src/rainbow/algorithms/proofs/ahof/spsa.clj) | AHoF O7 SPSA (Simultaneous Perturbation Stochastic Approximation): estimate the\n gradient from the two-sided perturbation difference (f(x+cD) - f(x-cD))/(2cD); with\n 2cD=1 the numerator is perturbation-difference f-plu |
| [`rainbow.algorithms.proofs.ahof.state-abstraction`](../src/rainbow/algorithms/proofs/ahof/state_abstraction.clj) | AHoF V52 Discrete State Abstraction (classical: map concrete states to abstract cells of a partition). |
| [`rainbow.algorithms.proofs.ahof.stieltjes`](../src/rainbow/algorithms/proofs/ahof/stieltjes.clj) | Stieltjes three-term recurrence for orthogonal polynomials (Kochenderfer Optimization O21.3), a signed-cluster algorithm deferred in August until the signed layer landed. |
| [`rainbow.algorithms.proofs.ahof.stl-monitor`](../src/rainbow/algorithms/proofs/ahof/stl_monitor.clj) | AHoF V63 Runtime STL Monitor: online monitoring of a Signal Temporal Logic specification. |
| [`rainbow.algorithms.proofs.ahof.stl-robustness`](../src/rainbow/algorithms/proofs/ahof/stl_robustness.clj) | AHoF V6 worked signal-temporal-logic robustness over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.strong-wolfe`](../src/rainbow/algorithms/proofs/ahof/strong_wolfe.clj) | AHoF O15 Strong Wolfe Line Search: accept a step only when it satisfies both the Armijo sufficient-decrease condition and the curvature condition: wolfe-ok? |
| [`rainbow.algorithms.proofs.ahof.subset-sum`](../src/rainbow/algorithms/proofs/ahof/subset_sum.clj) | AHoF Subset Sum (dynamic programming): decide whether some subset of a set of positive integers sums to a target -- the canonical (weakly) NP-complete decision problem and the kernel of the partition problem and 0/1-knap |
| [`rainbow.algorithms.proofs.ahof.support-function`](../src/rainbow/algorithms/proofs/ahof/support_function.clj) | AHoF V37 Support Function Method: represent a convex reachable set by its support function; a halfspace in a direction is respected when the set's support value in that direction is within the halfspace bound: within-sup |
| [`rainbow.algorithms.proofs.ahof.surrogate-explanation`](../src/rainbow/algorithms/proofs/ahof/surrogate_explanation.clj) | AHoF V56 Surrogate Model Explanation: fit an interpretable surrogate to a black-box model and explain via the surrogate; the explanation is faithful when the surrogate's local fidelity error is within the tolerance: fait |
| [`rainbow.algorithms.proofs.ahof.svm`](../src/rainbow/algorithms/proofs/ahof/svm.clj) | AHoF Support Vector Machine (linear, hard-margin classification): find the hyperplane that separates two classes with the MAXIMUM margin, then classify a point by which side it falls on. |
| [`rainbow.algorithms.proofs.ahof.symbolic-reachability`](../src/rainbow/algorithms/proofs/ahof/symbolic_reachability.clj) | AHoF V49 Symbolic Reachability (BDDs): represent reachable state sets symbolically (e.g. |
| [`rainbow.algorithms.proofs.ahof.tabu-search`](../src/rainbow/algorithms/proofs/ahof/tabu_search.clj) | AHoF Tabu Search: a local-search metaheuristic that escapes local optima by ALWAYS moving to the best neighbor -- even a worsening one -- while a short-term memory (the TABU LIST) forbids reversing recent moves, preventi |
| [`rainbow.algorithms.proofs.ahof.taylor-model`](../src/rainbow/algorithms/proofs/ahof/taylor_model.clj) | AHoF V43 Taylor Model Propagation: represent a function by a polynomial plus a guaranteed remainder interval and propagate it; the model is valid when the remainder magnitude stays within the bound: remainder-bounded? |
| [`rainbow.algorithms.proofs.ahof.thompson`](../src/rainbow/algorithms/proofs/ahof/thompson.clj) | AHoF Thompson Sampling (posterior sampling) for multi-armed bandits: instead of an explicit exploration bonus, draw one sample from each arm's posterior over its mean reward and pull the arm with the largest sample. |
| [`rainbow.algorithms.proofs.ahof.topological-sort`](../src/rainbow/algorithms/proofs/ahof/topological_sort.clj) | AHoF Topological Sort (Kahn's algorithm): order the vertices of a DAG so every edge points forward -- the canonical dependency/scheduling order. |
| [`rainbow.algorithms.proofs.ahof.tree-search-fal`](../src/rainbow/algorithms/proofs/ahof/tree_search_fal.clj) | AHoF V17 Tree Search for Falsification: best-first search over behaviours toward a violation, expanding the node with the lowest cost-to-violation; it keeps the smaller value: prefers-lower-cost? |
| [`rainbow.algorithms.proofs.ahof.trie`](../src/rainbow/algorithms/proofs/ahof/trie.clj) | AHoF Trie (prefix tree): store a set of strings in a tree keyed by characters, so that insertion and lookup are O(length) regardless of how many words are stored, and every shared prefix is stored once -- the workhorse b |
| [`rainbow.algorithms.proofs.ahof.trpo`](../src/rainbow/algorithms/proofs/ahof/trpo.clj) | AHoF D51 Trust-Region Policy Optimization: improve a policy by maximizing a surrogate advantage objective subject to a trust-region constraint that the new policy stays close to the old one in KL divergence. |
| [`rainbow.algorithms.proofs.ahof.trust-region`](../src/rainbow/algorithms/proofs/ahof/trust_region.clj) | AHoF O16 worked trust region step acceptance over exact rationals. |
| [`rainbow.algorithms.proofs.ahof.tsp-nearest-neighbor`](../src/rainbow/algorithms/proofs/ahof/tsp_nearest_neighbor.clj) | AHoF Nearest-Neighbor TSP heuristic: build a tour of the Travelling Salesman Problem by starting at a city and repeatedly travelling to the NEAREST unvisited city, returning to the start at the end. |
| [`rainbow.algorithms.proofs.ahof.two-pointers`](../src/rainbow/algorithms/proofs/ahof/two_pointers.clj) | AHoF Two Pointers: solve many array/string problems in a single O(n) pass by maintaining two indices that move toward each other (or in tandem) instead of nesting loops. |
| [`rainbow.algorithms.proofs.ahof.ucb`](../src/rainbow/algorithms/proofs/ahof/ucb.clj) | AHoF O64 Upper Confidence Bound acquisition (Bayesian optimization / bandits): select the next query by optimistically combining the surrogate's predicted mean with an exploration bonus proportional to the predictive unc |
| [`rainbow.algorithms.proofs.ahof.ucb1`](../src/rainbow/algorithms/proofs/ahof/ucb1.clj) | AHoF D57 UCB1 (bandit arm selection): pull the arm with the largest upper- confidence-bound score UCB_i = mean_i + sqrt(2 ln t / n_i). |
| [`rainbow.algorithms.proofs.ahof.ukf`](../src/rainbow/algorithms/proofs/ahof/ukf.clj) | AHoF D69 Unscented Kalman Filter: propagate a small set of deterministically chosen sigma points through the nonlinear model and recover the posterior mean as their weighted average. |
| [`rainbow.algorithms.proofs.ahof.union-by-rank`](../src/rainbow/algorithms/proofs/ahof/union_by_rank.clj) | AHoF Union by Rank: the balancing optimization that keeps a Union-Find (disjoint set) forest shallow, so find/union run in near-constant amortized time (inverse Ackermann, with path compression). |
| [`rainbow.algorithms.proofs.ahof.union-find`](../src/rainbow/algorithms/proofs/ahof/union_find.clj) | AHoF Union-Find (Disjoint-Set) connectivity: maintain a partition of elements into disjoint sets under union operations, answering connectivity queries by comparing set representatives. |
| [`rainbow.algorithms.proofs.ahof.value-iteration`](../src/rainbow/algorithms/proofs/ahof/value_iteration.clj) | AHoF D22 worked finite exact-rational value-iteration instance. |
| [`rainbow.algorithms.proofs.ahof.value-of-information`](../src/rainbow/algorithms/proofs/ahof/value_of_information.clj) | AHoF D19 worked value of information over signed rationals. |
| [`rainbow.algorithms.proofs.ahof.variable-elimination`](../src/rainbow/algorithms/proofs/ahof/variable_elimination.clj) | AHoF D3 Variable Elimination: exact inference by successively eliminating (marginalizing out) variables from the factor graph. |
| [`rainbow.algorithms.proofs.ahof.viterbi`](../src/rainbow/algorithms/proofs/ahof/viterbi.clj) | AHoF Viterbi Algorithm: find the single most-likely hidden-state sequence of a Hidden Markov Model given observations -- the standard decoder for HMMs (speech recognition, POS tagging, gene finding). |
| [`rainbow.algorithms.proofs.ahof.weighted-estimators`](../src/rainbow/algorithms/proofs/ahof/weighted_estimators.clj) | Kochenderfer weighted-sum / additive estimators (across Optimization and Validation) as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog: V7.4 multiple importance sampling : balance-w |
| [`rainbow.algorithms.proofs.ahof.weighted-interval`](../src/rainbow/algorithms/proofs/ahof/weighted_interval.clj) | AHoF Weighted Interval Scheduling (dynamic programming): given intervals with weights (values), select a mutually-compatible subset of MAXIMUM total weight. |
| [`rainbow.algorithms.proofs.ahof.weighted-sum`](../src/rainbow/algorithms/proofs/ahof/weighted_sum.clj) | AHoF O66 Weighted Sum Method (multi-objective scalarization): collapse several objectives into one scalar by a weighted sum, then optimize the scalar: scalarize w1 f1 w2 f2 = w1 * f1 + w2 * f2. |
| [`rainbow.algorithms.proofs.ahof.word-break`](../src/rainbow/algorithms/proofs/ahof/word_break.clj) | AHoF Word Break (dynamic programming): decide whether a string can be segmented into a sequence of dictionary words -- the core of tokenizers, CJK word segmentation, and URL/identifier splitting. |
| [`rainbow.algorithms.proofs.ahof.z-score`](../src/rainbow/algorithms/proofs/ahof/z_score.clj) | AHoF Z-Score Standardization: rescale a feature to zero mean and unit standard deviation, z = (x - mean) / std-dev -- the standard preprocessing step that puts features on a comparable scale (essential for distance-based |
| [`rainbow.algorithms.proofs.ahof.zonotope`](../src/rainbow/algorithms/proofs/ahof/zonotope.clj) | AHoF V35 Zonotope Propagation: represent a reachable set as a zonotope (center plus generator vectors) and propagate it; a point lies in the zonotope when each generator coordinate stays within its unit bound: in-zonotop |

## Graph algorithms (`src/rainbow/algorithms/proofs/graph/`, 8)

| namespace | |
|---|---|
| [`rainbow.algorithms.proofs.graph.bellman-ford-convergence-attained`](../src/rainbow/algorithms/proofs/graph/bellman_ford_convergence_attained.clj) | BELLMAN-FORD CONVERGENCE, ATTAINMENT HALF (second half, part (R)). |
| [`rainbow.algorithms.proofs.graph.bellman-ford-convergence-upper`](../src/rainbow/algorithms/proofs/graph/bellman_ford_convergence_upper.clj) | BELLMAN-FORD CONVERGENCE, UPPER HALF (second half, part (U)). |
| [`rainbow.algorithms.proofs.graph.dijkstra-invariant`](../src/rainbow/algorithms/proofs/graph/dijkstra_invariant.clj) | DIJKSTRA'S INVARIANT (the Dijkstra step family's Level-3 half). |
| [`rainbow.algorithms.proofs.graph.floyd-warshall-convergence-attained`](../src/rainbow/algorithms/proofs/graph/floyd_warshall_convergence_attained.clj) | FLOYD-WARSHALL, ATTAINMENT HALF (second half, part (R)). |
| [`rainbow.algorithms.proofs.graph.floyd-warshall-convergence-upper`](../src/rainbow/algorithms/proofs/graph/floyd_warshall_convergence_upper.clj) | FLOYD-WARSHALL INVARIANT, UPPER HALF (part (U)). |
| [`rainbow.algorithms.proofs.graph.walk-concat`](../src/rainbow/algorithms/proofs/graph/walk_concat.clj) | CONCATENATING WALKS, for the Floyd-Warshall invariant. |
| [`rainbow.algorithms.proofs.graph.walk-cycle-cut`](../src/rainbow/algorithms/proofs/graph/walk_cycle_cut.clj) | CUTTING A CYCLE OUT OF A WALK, the step of the Bellman-Ford cycle-removal lemma. |
| [`rainbow.algorithms.proofs.graph.walk-shorten`](../src/rainbow/algorithms/proofs/graph/walk_shorten.clj) | CYCLE REMOVAL: without negative closed walks, every walk over n nodes can be replaced by one of FEWER THAN n arcs with the same ends that is no longer: signed/walk-shorten : no-negative-cycles n W -> forall k x, (forall  |

## Data types (`src/rainbow/data/`, 1)

| namespace | |
|---|---|
| [`rainbow.data.binary`](../src/rainbow/data/binary.clj) | Binary (positional) numerals -- foundation stone for magnitude-INDEPENDENT arithmetic. |
