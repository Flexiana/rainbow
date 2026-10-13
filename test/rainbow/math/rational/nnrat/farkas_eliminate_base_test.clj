(ns rainbow.math.rational.nnrat.farkas-eliminate-base-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-eliminate-base :as eb]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (eb/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest fully-reduced-constraint-is-a-constant-comparison
  (testing "the over-variable recursion's base case: a 0-variable both-sides
            constraint eval(nil)+c_L <= eval(nil)+c_R reduces to c_L <= c_R
            (eval of the empty vector is zero definitionally, 0+x~x). This is
            Feasible 0. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (eb/definition-ids env) (eb/theorem-ids env))]
      (is (= #{'nnrat/farkas-eliminate-base} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
