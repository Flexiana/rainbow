(ns rainbow.algorithms.proofs.ahof.lcs-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.lcs :as lcs]
            [rainbow.algorithms.reference.lcs :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lcs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest lcs-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lcs/definition-ids checked-environment)
        theorems (lcs/theorem-ids checked-environment)]
    (is (= #{'lcs/cell} (set (keys definitions))))
    (is (= #{'lcs/match-extends-diagonal 'lcs/mismatch-takes-max
             'lcs/dominates-left-neighbor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-lcs
  (is (= 3 (executable/cell true 2 9 9)))
  (is (= 3 (executable/cell false 5 2 3)))
  ;; LCS of ABCBDAB and BDCAB is 4 (e.g. BCAB)
  (is (= 4 (executable/lcs-length "ABCBDAB" "BDCAB"))))
