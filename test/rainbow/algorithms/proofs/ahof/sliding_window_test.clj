(ns rainbow.algorithms.proofs.ahof.sliding-window-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.sliding-window :as sw]
            [rainbow.algorithms.reference.sliding-window :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sw/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest sliding-window-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sw/definition-ids checked-environment)
        theorems (sw/theorem-ids checked-environment)]
    (is (= #{'sliding-window/window-valid?} (set (keys definitions))))
    (is (= #{'sliding-window/within-budget-valid
             'sliding-window/valid-window-within-limit
             'sliding-window/over-budget-invalid}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-sliding-window
  (is (true? (executable/window-valid? 3 5)))
  (is (false? (executable/window-valid? 8 5)))
  ;; max sum of window size 3 in [2 1 5 1 3 2] is 9 (5+1+3)
  (is (= 9 (executable/max-window-sum [2 1 5 1 3 2] 3)))
  ;; longest subarray of [1 2 1 0 1 1] with sum <= 3
  (is (= 4 (executable/longest-within-budget [1 2 1 0 1 1] 3))))
