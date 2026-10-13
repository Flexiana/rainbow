(ns rainbow.math.rational.nnrat.farkas-recursion-step-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-recursion-step :as step]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (step/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest one-elimination-round-yields-a-feasible-reduced-system
  (testing "piece (ii) recursion step: composing eliminate-structured and
            the dependent partition, one full round takes structured cross
            rows holding at w to EXISTS (lowers, uppers) with brick 5b/4
            folds holding -- the step the variable-count induction folds.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (step/definition-ids env) (step/theorem-ids env))]
      (is (= #{'nnrat/farkas-recursion-step} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
