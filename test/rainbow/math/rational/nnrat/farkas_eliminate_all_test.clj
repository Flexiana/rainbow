(ns rainbow.math.rational.nnrat.farkas-eliminate-all-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-eliminate-all :as ea]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (ea/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest over-variable-recursion-eliminates-all-variables
  (testing "the over-variable recursion: nnrat/farkas-eliminate-all folds an
            elimination step (Feasible (k+1) -> Feasible k) over a variable
            count n, concluding Feasible 0 from Feasible n -- Nat.rec, base
            identity, successor applies step then IH. The n-variable LP
            feasibility induction skeleton. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (ea/definition-ids env) (ea/theorem-ids env))]
      (is (= #{'nnrat/farkas-eliminate-all} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
