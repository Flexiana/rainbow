(ns rainbow.algorithms.proofs.counterfactual-distance-separation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.counterfactual-distance-separation :as separation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (separation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest counterfactual-distance-separation-is-native-and-axiom-free
  (let [env @checked-environment
        ids (separation/theorem-ids env)]
    (is (= #{'signed/subtract-zero-reflects-equivalence
             'vector/subtract-zero-reflects-equivalence
             'counterfactual/distance-squared-nonnegative
             'counterfactual/equivalent-of-distance-squared-zero}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
