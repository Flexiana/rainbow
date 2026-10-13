(ns rainbow.algorithms.proofs.ahof.variable-elimination-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.variable-elimination :as ve]
            [rainbow.algorithms.reference.variable-elimination :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ve/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest variable-elimination-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ve/definition-ids checked-environment)
        theorems (ve/theorem-ids checked-environment)]
    (is (= #{'variable-elimination/marginalize} (set (keys definitions))))
    (is (= #{'variable-elimination/marginalize-unfold
             'variable-elimination/marginalize-example
             'variable-elimination/marginal-dominates-slice}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-variable-elimination-marginalizes
  (is (= 7 (executable/marginalize 3 4)))
  ;; Eliminate x from a joint over {x, y}: marginal over y sums the x-slices.
  (let [factor {{:x true :y true} 3, {:x false :y true} 4
                {:x true :y false} 1, {:x false :y false} 2}
        marginal (executable/eliminate factor :x)]
    (is (= 7 (marginal {:y true})))
    (is (= 3 (marginal {:y false})))))
