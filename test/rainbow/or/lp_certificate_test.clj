(ns rainbow.or.lp-certificate-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]))

(def base
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lp-on/extend-environment
          decide-order/extend-environment))))

;; maximize 2*x0 - x1  s.t.  x0 + x1 <= 4,  x0 <= 3,  x >= 0
;; optimum x = (3, 0) with value 6; dual y = (0, 2)
(def penalty-mix
  {:matrix [[1 1] [1 0]]
   :capacities [4 3]
   :margins [2 -1]
   :plan [3 0]
   :prices [0 2]})

(deftest a-two-variable-instance-with-a-penalty-is-certified
  (let [result (lp/certify @base penalty-mix)]
    (is (= :certified (:status result)))
    (is (= 6 (:objective result)))
    (testing "and the proof rests on no axioms"
      (is (every? empty? (map :axioms (vals (:declarations result))))))))

;; three products, three constraints, a penalty and a FRACTIONAL dual price
;; maximize 3*x0 + 1*x1 - 2*x2
;;   s.t. x0 + x1 + x2 <= 10,  2*x0 <= 8,  x1 <= 5,  x >= 0
;; optimum x = (4, 5, 0) with value 17. The shared capacity is slack at 9 < 10,
;; so complementary slackness prices it at zero; the two binding limits carry
;; the margin at y = (0, 3/2, 1), and 8*3/2 + 5*1 = 17 closes the gap exactly --
;; which only works because the arithmetic is exact rationals rather than floats.
(def three-by-three
  {:matrix [[1 1 1] [2 0 0] [0 1 0]]
   :capacities [10 8 5]
   :margins [3 1 -2]
   :plan [4 5 0]
   :prices [0 3/2 1]})

(deftest a-larger-instance-is-certified-through-the-same-theorem
  (let [result (lp/certify @base three-by-three
                           {:alias 'optimization/three-by-three-optimal})]
    (is (= :certified (:status result)))
    (is (= 17 (:objective result)))
    (is (= 3 (:rows result)))
    (is (= 3 (:columns result)))
    (testing "the index type is not fixed to the instance size"
      (is (every? empty? (map :axioms (vals (:declarations result))))))))

(deftest a-suboptimal-plan-is-refused
  (testing "x = (2, 0) is feasible but scores 4, so y = (0, 2) cannot certify it"
    (let [result (lp/certify @base (assoc penalty-mix :plan [2 0])
                             {:alias 'optimization/suboptimal-refused})]
      (is (= :rejected (:status result))))))

(deftest an-infeasible-plan-is-refused
  (testing "x = (5, 0) violates x0 <= 3"
    (let [result (lp/certify @base (assoc penalty-mix :plan [5 0])
                             {:alias 'optimization/infeasible-refused})]
      (is (= :rejected (:status result))))))

(deftest a-dual-vector-that-does-not-close-the-gap-is-refused
  (testing "y = (0, 3) is dual feasible but prices the bound at 9, not 6"
    (let [result (lp/certify @base (assoc penalty-mix :prices [0 3])
                             {:alias 'optimization/loose-dual-refused})]
      (is (= :rejected (:status result))))))

;; ---- R2: a bound that holds even when the plan is not optimal ---------------

(deftest a-suboptimal-plan-still-gets-a-proved-bound
  (testing "a truncated solve returns x = (2, 0), worth 4, with prices (0, 2)"
    (let [result (lp/bound @base (assoc penalty-mix :plan [2 0])
                           {:alias 'optimization/truncated-bound})]
      (is (= :bounded (:status result)))
      (is (= 4 (:achieved result)))
      (is (= 6 (:bound result)))
      (testing "so the buyer learns the plan is within 2 of anything achievable"
        (is (= 2 (:gap result))))
      (is (every? empty? (map :axioms (vals (:declarations result))))))))

(deftest an-optimal-plan-bounds-with-zero-gap
  (let [result (lp/bound @base penalty-mix {:alias 'optimization/tight-bound})]
    (is (= :bounded (:status result)))
    (is (= 0 (:gap result)))))

(deftest a-bound-still-requires-a-feasible-plan-and-a-dual-feasible-price
  (testing "an infeasible plan has no bound to prove"
    (is (= :rejected (:status (lp/bound @base (assoc penalty-mix :plan [5 0])
                                        {:alias 'optimization/bad-bound})))))
  (testing "prices that are not dual feasible cannot bound anything"
    (is (= :rejected (:status (lp/bound @base (assoc penalty-mix :prices [0 0])
                                        {:alias 'optimization/no-price-bound}))))))

(deftest the-check-is-content-addressed-for-audit
  (let [once (lp/certify @base penalty-mix {:alias 'optimization/audit-a})
        twice (lp/certify @base penalty-mix {:alias 'optimization/audit-a})
        changed (lp/certify @base (assoc penalty-mix :capacities [5 3])
                            {:alias 'optimization/audit-a})]
    (testing "the same instance and result always give the same audit id"
      (is (= (:audit/id once) (:audit/id twice)))
      (is (string? (:audit/id once))))
    (testing "changing the data changes the id"
      (is (not= (:audit/id once) (:audit/id changed))))))

;; ---- the first wedge: project portfolio under capacity ----------------------
;;
;; three projects worth 5, 4 and 6 costing 2, 3 and 4 against a capacity of 5,
;; each selectable at most once. The best INTEGRAL selection is projects 0 and 1,
;; worth 9. The linear relaxation does better -- project 0 whole plus three
;; quarters of project 2, worth 19/2 -- so 19/2 is the number that prunes the
;; branch-and-bound tree, and the submitted integral plan is provably within 1/2.
(def portfolio
  {:matrix [[2 3 4] [1 0 0] [0 1 0] [0 0 1]]
   :capacities [5 1 1 1]
   :margins [5 4 6]
   :plan [1 1 0]
   :prices [3/2 2 0 0]})

(deftest a-project-portfolio-gets-a-pruning-bound
  (let [result (lp/bound @base portfolio {:alias 'optimization/portfolio-bound})]
    (is (= :bounded (:status result)))
    (is (= 9 (:achieved result)))
    (is (= 19/2 (:bound result)))
    (testing "the integral plan is provably within one half of anything feasible"
      (is (= 1/2 (:gap result))))
    (testing "and the bound is proved for EVERY feasible plan, not just this one"
      (is (contains? (:declarations result)
                     'optimization/portfolio-bound-universal))
      (is (= :checked (get-in result [:declarations
                                      'optimization/portfolio-bound-universal
                                      :status]))))
    (is (every? empty? (map :axioms (vals (:declarations result)))))))

;; ---- cost minimization with a covering constraint ---------------------------
;;
;; minimize 2*x0 + 3*x1 subject to x0 + x1 >= 4, x >= 0.
;; A covering constraint is written as (-1)*x0 + (-1)*x1 <= -4, which needs
;; negative coefficients on BOTH the matrix and the right-hand side -- neither is
;; expressible in the nnrat stack. The cheapest way to cover 4 units is four of
;; product 0 at cost 8, and the shadow price of the requirement is 2.
(def min-cost
  {:sense :minimize
   :matrix [[-1 -1]]
   :capacities [-4]
   :margins [2 3]
   :plan [4 0]
   :prices [2]})

(deftest a-cost-problem-is-bounded-from-below
  (let [result (lp/bound @base min-cost {:alias 'optimization/min-cost-bound})]
    (is (= :bounded (:status result)))
    (is (= :minimize (:sense result)))
    (is (= 8 (:achieved result)))
    (testing "the proved quantity is a floor on cost, not a ceiling"
      (is (= :lower (:direction result)))
      (is (= 8 (:bound result)))
      (is (= 0 (:gap result))))
    (is (every? empty? (map :axioms (vals (:declarations result)))))))

(deftest a-cost-problem-certifies-optimality-too
  (let [result (lp/certify @base min-cost {:alias 'optimization/min-cost-optimal})]
    (is (= :certified (:status result)))
    (is (= :minimize (:sense result)))
    (is (= 8 (:objective result)))))

(deftest maximization-is-still-the-default-and-unchanged
  (let [result (lp/bound @base penalty-mix {:alias 'optimization/still-maximize})]
    (is (= :maximize (:sense result)))
    (is (= :upper (:direction result)))
    (is (= 6 (:bound result)))))

;; ---- equality constraints with a free dual price ---------------------------
;;
;; minimize 2*x0 + 5*x1 subject to x0 + x1 = 10, x0 <= 6, x >= 0.
;; A blend that must total exactly ten units, where the cheap input is capped at
;; six. The optimum takes all six cheap units and four expensive ones, costing
;; 32. The balance constraint's dual price is NEGATIVE (-5) -- which is what a
;; free dual means and why equalities cannot be modelled with nonnegative prices.
(def blend
  {:sense :minimize
   :matrix [[1 0]]
   :capacities [6]
   :equalities [{:row [1 1] :value 10}]
   :equality-prices [-5]
   :margins [2 5]
   :plan [6 4]
   :prices [3]})

(deftest an-equality-constrained-blend-is-certified
  (let [result (lp/bound @base blend {:alias 'optimization/blend-bound})]
    (is (= :bounded (:status result)))
    (is (= 32 (:achieved result)))
    (testing "the free dual reproduces the exact cost floor"
      (is (= :lower (:direction result)))
      (is (= 32 (:bound result)))
      (is (= 0 (:gap result))))
    (is (every? empty? (map :axioms (vals (:declarations result)))))))

(deftest an-equality-needs-exactly-one-free-price
  (is (= :rejected
         (:status (lp/bound @base (assoc blend :equality-prices [])
                            {:alias 'optimization/blend-mismatch})))))

(deftest violating-an-equality-is-refused
  (testing "a plan totalling 9 instead of 10 breaks the balance row"
    (is (= :rejected
           (:status (lp/bound @base (assoc blend :plan [6 3])
                              {:alias 'optimization/blend-violated}))))))

;; ---- a first-wedge sized instance ------------------------------------------
;;
;; Five candidate projects competing for two shared resources, each project
;; selectable at most once: seven rows by five columns. The submitted selection
;; takes projects 0, 1 and 2, using 6 of 7 units of the first resource and all 6
;; of the second, and is worth 22. The dual prices both resources and the three
;; binding selection limits, proving nothing feasible -- integral or fractional --
;; exceeds 24.
(def five-project-portfolio
  {:matrix [[3 2 1 4 2]
            [1 3 2 1 3]
            [1 0 0 0 0]
            [0 1 0 0 0]
            [0 0 1 0 0]
            [0 0 0 1 0]
            [0 0 0 0 1]]
   :capacities [7 6 1 1 1 1 1]
   :margins [10 7 5 9 4]
   :plan [1 1 1 0 0]
   :prices [2 1 3 0 1 0 0]})

(deftest a-five-project-two-resource-portfolio-is-bounded
  (let [result (lp/bound @base five-project-portfolio
                         {:alias 'optimization/five-project-bound})]
    (is (= :bounded (:status result)))
    (is (= 7 (:rows result)))
    (is (= 5 (:columns result)))
    (is (= 22 (:achieved result)))
    (is (= 24 (:bound result)))
    (testing "the selection is provably within 2 of anything feasible"
      (is (= 2 (:gap result))))
    (testing "the bound covers every feasible plan, so it prunes the tree"
      (is (= :checked (get-in result [:declarations
                                      'optimization/five-project-bound-universal
                                      :status]))))
    (is (every? empty? (map :axioms (vals (:declarations result)))))))

;; ---- R6: the artifact an auditor receives ----------------------------------

(deftest an-audit-bundle-is-self-contained-and-serializable
  (let [result (lp/certify @base penalty-mix {:alias 'optimization/audited})
        bundle (lp/audit-bundle result "sha256:environment-under-test")
        round-tripped (read-string (pr-str bundle))]
    (testing "the bundle carries the verdict, the data and the provenance"
      (is (= :certified (:status bundle)))
      (is (= penalty-mix (:instance bundle)))
      (is (= "sha256:environment-under-test" (:audit/environment-id bundle)))
      (is (string? (:audit/id bundle))))
    (testing "an auditor can confirm the proof rests on nothing"
      (is (every? empty? (map :axioms (vals (:declarations bundle))))))
    (testing "no live objects survive, so it can be written and read back"
      (is (nil? (:environment bundle)))
      (is (= (:audit/id bundle) (:audit/id round-tripped)))
      (is (= (:status bundle) (:status round-tripped))))))


;; ---- second wedge: order acceptance with batch setup ------------------------
;;
;; Two orders sharing a first time window, a third in a second window, and a
;; setup that the third order requires. Decision vector is (x0 x1 x2 y).
;;
;;   maximize 8x0 + 6x1 + 9x2 - 2y
;;   window 1   4x0 + 5x1        <= 10
;;   window 2              6x2   <= 8
;;   each order and the setup at most one
;;   linking    x2 - y <= 0
;;
;; The linking row is the point: "you may only run this order if you paid the
;; setup" is an ORDINARY row once a coefficient may be negative. Time windows are
;; ordinary capacity rows. Sequencing and precedence have the same [1 -1] shape.
;; So the second wedge needs no new encoding -- only signed coefficients, which
;; the nnrat stack could not have supplied.
(def order-acceptance
  {:matrix [[4 5 0 0]
            [0 0 6 0]
            [1 0 0 0]
            [0 1 0 0]
            [0 0 1 0]
            [0 0 1 -1]
            [0 0 0 1]]
   :capacities [10 8 1 1 1 0 1]
   :margins [8 6 9 -2]
   :plan [1 1 1 1]
   :prices [0 0 8 6 9 0 0]})

(deftest order-acceptance-with-batching-goes-through-as-ordinary-rows
  (let [result (lp/bound @base order-acceptance
                         {:alias 'optimization/order-acceptance-bound})]
    (testing "time windows, order limits and batch linking all check"
      (is (= :bounded (:status result)))
      (is (= 7 (:rows result)))
      (is (= 4 (:columns result))))
    (testing "the accepted schedule is worth 21 after the setup penalty"
      (is (= 21 (:achieved result))))
    (testing "and no feasible schedule beats the proved bound"
      (is (= 23 (:bound result)))
      (is (= 2 (:gap result))))
    (is (every? empty? (map :axioms (vals (:declarations result)))))))

(deftest a-schedule-that-skips-the-setup-it-needs-is-refused
  (testing "accepting order 2 with y = 0 violates the linking row x2 - y <= 0"
    (is (= :rejected
           (:status (lp/bound @base (assoc order-acceptance :plan [1 1 1 0])
                              {:alias 'optimization/setup-skipped}))))))


;; ---- refusals say WHY -------------------------------------------------------
;;
;; A checker that refused everything the same way would be nearly as bad as one
;; that accepted everything: a caller cannot tell a false certificate from an
;; instance the kernel could not finish reducing. `bound` surfaces the kernel's
;; own category alongside the refusal.
;;
;; The reduction budget is a real ceiling and it is documented in
;; the design notes with the measured sizes rather than asserted here --
;; exhausting the budget on purpose costs minutes per run, which is not a price
;; a suite should pay to restate a number.
(deftest a-refusal-reports-the-kernel-category
  (let [dual-infeasible (assoc order-acceptance :prices [0 0 0 0 0 0 0])
        result (lp/bound @base dual-infeasible
                         {:alias 'optimization/why-refused})]
    (is (= :rejected (:status result)))
    (is (= :kernel/type-mismatch (:kernel/category result)))))

;; ---- the reduction budget ---------------------------------------------------
;;
;; The budget is a TERMINATION safeguard, not a soundness one. It bounds how long
;; the kernel computes and has no bearing on what it accepts. These tests pin
;; that distinction down, because `the design notes` now tells a buyer they
;; may raise it, and a budget that could buy acceptance would make that advice
;; dangerous rather than merely slow.

(deftest raising-the-budget-cannot-buy-acceptance
  (testing "a dual-infeasible instance stays refused at forty times the budget"
    (let [dual-infeasible (assoc order-acceptance :prices [0 0 0 0 0 0 0])
          result (lp/bound @base dual-infeasible
                           {:alias 'optimization/budget-cannot-buy-acceptance
                            :reductions 40000000})]
      (is (= :rejected (:status result)))
      ;; still the TYPE error, not a resource one: the extra budget let the
      ;; kernel finish the reduction and reject on the merits
      (is (= :kernel/type-mismatch (:kernel/category result))))))

(deftest a-starved-budget-refuses-rather-than-mis-certifying
  (testing "too small a budget reports resource exhaustion, never :bounded"
    ;; preflight? false so this exercises the KERNEL's own refusal; the
    ;; prediction path has its own test and would otherwise refuse first
    (let [result (lp/bound @base order-acceptance
                           {:alias 'optimization/starved-budget
                            :preflight? false
                            :reductions 0})]
      (is (= :rejected (:status result)))
      (is (= :kernel/resource-limit (:kernel/category result))))))

(deftest the-budget-used-is-reported
  (testing "a caller can see which budget produced the verdict"
    (let [result (lp/bound @base order-acceptance
                           {:alias 'optimization/budget-reported
                            :reductions 2000000})]
      (is (= :bounded (:status result)))
      (is (= 2000000 (:reductions result))))))

;; ---- the reach boundary, end to end -----------------------------------------
;;
;; These run the REAL pipeline against the real checkpoint, not the cost model in
;; isolation. That distinction has earned its keep in this repo: a unit test on
;; `preflight` would pass even if the wiring into `bound` were wrong, and it was
;; a full end-to-end run -- not a focused one -- that caught the trusted-base
;; regression earlier in this work.
;;
;; What they pin is the finding that fractional data, not size, is what puts an
;; instance out of reach. The kernel's nnrat arithmetic never reduces to lowest
;; terms, so summing n terms with denominator d yields d^n. Measured: at four
;; terms, denominator 2 costs 32768x the integer magnitude and denominator 4
;; costs on the order of 10^11x. Both are refused; neither is mis-certified.

(defn- box-instance
  "n boxed variables with a known exact optimum: take every capacity, and price
  each row at its own margin. Feasible, dual feasible and zero-gap by
  construction at every parameter setting."
  [n magnitude denominator]
  (let [c (mapv (fn [j] (/ (* magnitude (inc (mod j 4))) denominator)) (range n))
        u (mapv (fn [j] (* magnitude (inc (mod j 3)))) (range n))]
    {:matrix (mapv (fn [i] (mapv (fn [j] (if (= i j) 1 0)) (range n))) (range n))
     :capacities u :margins c :plan u :prices c}))

(deftest fractional-data-is-never-refused-on-a-prediction
  ;; This test asserted the opposite until a probe showed the prediction was
  ;; wrong by three orders of magnitude on fractional data: a three-variable
  ;; instance with denominator 2 estimates 3.3 BILLION and the kernel checks it
  ;; in 151s. Refusing it withheld a certificate that was available. The model
  ;; over-states fractional cost because it computes the UNREDUCED cross product,
  ;; where a denominator d over n terms contributes d^n; the kernel does not pay
  ;; that. So fractional instances go to the kernel, whatever the model thinks.
  (testing "an instance the model calls hopeless is still checked, and passes"
    (let [instance (box-instance 3 1 2)
          estimate (lp/preflight instance 1000000)]
      (is (= :over-budget (:verdict estimate))
          "the model does predict this one is hopeless")
      (let [result (lp/bound @base instance
                             {:alias 'optimization/fractional-not-refused})]
        (is (= :bounded (:status result))
            "and the kernel checks it anyway, so it must not be refused"))))
  (testing "integral data, where the model is calibrated, may still be refused"
    (let [result (lp/bound @base (box-instance 4 32 1)
                           {:alias 'optimization/integral-refused})]
      (is (= :rejected (:status result)))
      (is (= :lp-certificate/predicted-over-budget (:error/category result))))))

(deftest the-cost-model-agrees-with-the-kernel-on-instances-it-accepts
  (testing "an instance preflight calls :fits really does check"
    (let [instance (box-instance 4 1 1)
          estimate (lp/preflight instance 1000000)]
      (is (= :fits (:verdict estimate)))
      (is (= :bounded (:status (lp/bound @base instance
                                         {:alias 'optimization/model-agrees}))))))
  (testing "preflight can be switched off, and then the kernel decides alone"
    (let [result (lp/bound @base (box-instance 4 1 2)
                           {:alias 'optimization/no-preflight
                            :preflight? false
                            :reductions 0})]
      ;; without the prediction this is the kernel's own resource refusal
      (is (= :rejected (:status result)))
      (is (= :kernel/resource-limit (:kernel/category result))))))

(deftest integerizing-is-exact-and-leaves-integral-data-untouched
  (testing "scaling removes every denominator"
    (let [[scaled scale] (lp/integerize (box-instance 4 1 2))]
      (is (= 2 scale))
      ;; `denominator` is defined only on Ratio, so a whole number must be
      ;; recognised by NOT being a ratio -- the same trap as `numerator`
      ;; throwing on Long, which is why the source has `rational-parts`
      (is (every? #(not (ratio? (rationalize %)))
                  (concat (apply concat (:matrix scaled)) (:capacities scaled)
                          (:margins scaled) (:plan scaled) (:prices scaled))))))
  (testing "integral data is returned unchanged, so its audit id is stable"
    (let [instance (box-instance 4 1 1)
          [scaled scale] (lp/integerize instance)]
      (is (= 1 scale))
      (is (= (mapv vec (:matrix instance)) (mapv vec (:matrix scaled))))
      (is (= (vec (:capacities instance)) (vec (:capacities scaled))))
      (is (= (vec (:margins instance)) (vec (:margins scaled)))))))

;; ---- scaling, and what it does to the audit trail ---------------------------
;;
;; `:integerize? true` makes the kernel check the SCALED instance. That is a
;; genuinely different proof about genuinely different numbers, so its content
;; id genuinely differs -- and it SHOULD. The id names the proof the kernel
;; accepted; reporting the unscaled instance's id would assert that something was
;; checked which was not. The id cannot be preserved without lying, which is why
;; scaling is opt-in rather than automatic.
;;
;; What CAN be preserved is auditability, and that is what these pin: the result
;; carries the scale, the instance actually checked, and the original, and the
;; reported numbers come back in the CALLER'S units rather than in units of D^3.

(def fractional-nine
  {:matrix [[4 5 0 0 0] [0 0 3 6 0] [1 0 0 0 0] [0 1 0 0 0] [0 0 1 0 0]
            [0 0 0 1 0] [0 0 1 0 -1] [0 0 0 1 -1] [0 0 0 0 1]]
   :capacities [10 8 1 1 1 1 0 0 1]
   :margins [8 6 5 9 -2]
   :plan [1 1 0 1 1]
   :prices [0 3/2 8 6 5 9 0 0 1/2]})

(deftest scaling-preserves-a-fractional-bound-and-reports-in-caller-units
  (testing "native arithmetic checks the unscaled fractional instance too"
    (let [result (lp/bound @base fractional-nine
                           {:alias 'optimization/fractional-unscaled
                            :preflight? false})]
      (is (= :bounded (:status result)))
      (is (= 81/2 (:bound result)))
      (is (= 1 (:integer-scale result)))
      (is (every? empty? (map :axioms (vals (:declarations result)))))))
  (testing "scaled, the instance still checks and reports the bound in original units"
    (let [result (lp/bound @base fractional-nine
                           {:alias 'optimization/fractional-scaled
                            :integerize? true
                            :preflight? false})]
      (is (= :bounded (:status result)))
      ;; the bound comes back in the caller's units, not multiplied by D^3
      (is (= 81/2 (:bound result)))
      (is (= 2 (:integer-scale result)))
      ;; the audit trail records both halves of the correspondence
      (is (= fractional-nine (:instance result)))
      (is (every? #(not (ratio? (rationalize %)))
                  (concat (apply concat (:matrix (:instance/checked result)))
                          (:capacities (:instance/checked result))
                          (:margins (:instance/checked result))))))))

(deftest scaling-integral-data-is-a-true-no-op
  (testing "integerize returns the very same value, not merely an equal one"
    ;; `identical?` and not `=`: multiplying by one produces an EQUAL instance
    ;; whose coefficients may be BigInt rather than Long, which serializes
    ;; differently and so changes the content id. That defect existed and this
    ;; is the assertion that pins it.
    (let [integral {:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]
                    :plan [3 0] :prices [0 2]}
          [scaled scale] (lp/integerize integral)]
      (is (= 1 scale))
      (is (identical? integral scaled))))
  (testing "so the audit id is unchanged by asking for it"
    ;; the SAME alias in both runs: the audit id covers declaration names, so
    ;; comparing two different aliases would differ for reasons having nothing
    ;; to do with scaling
    (let [integral {:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]
                    :plan [3 0] :prices [0 2]}
          plain (lp/bound @base integral {:alias 'optimization/id-stability})
          scaled (lp/bound @base integral {:alias 'optimization/id-stability
                                           :integerize? true})]
      (is (= :bounded (:status plain)))
      (is (= :bounded (:status scaled)))
      (is (= 1 (:integer-scale scaled)))
      (is (= (:audit/id plain) (:audit/id scaled))
          "scaling integral data must not disturb its identity"))))
