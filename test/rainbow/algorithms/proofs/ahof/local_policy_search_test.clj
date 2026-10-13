(ns rainbow.algorithms.proofs.ahof.local-policy-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.local-policy-search :as lps]
            [rainbow.algorithms.reference.local-policy-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lps/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest local-policy-search-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lps/definition-ids checked-environment)
        theorems (lps/theorem-ids checked-environment)]
    (is (= #{'local-policy-search/improve} (set (keys definitions))))
    (is (= #{'local-policy-search/improve-adopts-better
             'local-policy-search/improve-above-incumbent
             'local-policy-search/improve-above-neighbor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-local-policy-search-ascends
  (is (= 7 (executable/improve 5 7)))
  (is (= 5 (executable/improve 5 3)))
  ;; Maximizing -(theta-4)^2 by perturbing +1: climbs from 0 toward the optimum 4.
  (let [value (fn [t] (- (* (- t 4) (- t 4))))
        best (executable/search value inc 0 10)]
    (is (= 4 best))))
