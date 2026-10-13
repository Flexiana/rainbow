(ns rainbow.algorithms.proofs.ahof.two-pointers-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.two-pointers :as tp]
            [rainbow.algorithms.reference.two-pointers :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          tp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest two-pointers-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (tp/definition-ids checked-environment)
        theorems (tp/theorem-ids checked-environment)]
    (is (= #{'two-pointers/shrink-right?} (set (keys definitions))))
    (is (= #{'two-pointers/large-sum-shrinks-right
             'two-pointers/shrink-sum-at-least-target
             'two-pointers/small-sum-grows-left}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-two-pointers
  (is (true? (executable/shrink-right? 7 5)))
  (is (false? (executable/shrink-right? 3 5)))
  ;; sorted [1 2 4 7 11 15], target 15 -> indices [1 5] (4 + 11)
  (is (= [2 4] (executable/pair-sum [1 2 4 7 11 15] 15)))
  (is (nil? (executable/pair-sum [1 2 3] 100))))
