(ns rainbow.algorithms.proofs.ahof.chebyshev-scalarization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.chebyshev-scalarization :as chebyshev]
            [rainbow.algorithms.reference.chebyshev-scalarization :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          chebyshev/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest chebyshev-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (chebyshev/definition-ids checked-environment)
        theorems (chebyshev/theorem-ids checked-environment)]
    (is (= #{'chebyshev/scalarize} (set (keys definitions))))
    (is (= #{'chebyshev/scalarize-example 'chebyshev/dominates-first
             'chebyshev/dominates-second 'chebyshev/dominates-third}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-chebyshev-scalarizes
  (is (= 7 (executable/scalarize [3 7 2])))
  ;; weighted: max(2*1, 1*3, 3*2) = max(2, 3, 6) = 6
  (is (= 6 (executable/weighted-scalarize [2 1 3] [1 3 2]))))
