(ns rainbow.math.rational.nnrat.lp-two-var-strong-duality-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.lp-two-var-strong-duality :as lp]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lp/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest two-variable-strong-duality-via-fourier-motzkin
  (testing "brick 5d-iii of the general LP FM encoding: for the LP
            max x1 + 2*x2 s.t. x1 + x2 <= 1, primal optimum = dual
            optimum = 2, proved through actual variable elimination.
            lp-two-var-example-primal-optimal: every feasible (x1,x2) has
            x1 + 2*x2 <= 2, by ELIMINATING x1 (additive cross crux +
            both-sides conversion) then bounding x2.
            lp-two-var-example-strong-duality: the bound is tight -- (0,1)
            feasible, attains 2, dual y=2 gives b*y=2, zero gap. The first
            multi-variable LP strong duality via Fourier-Motzkin
            elimination. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (lp/definition-ids env) (lp/theorem-ids env))]
      (is (= #{'nnrat/lp-two-var-example-primal-optimal
               'nnrat/lp-two-var-example-strong-duality}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
