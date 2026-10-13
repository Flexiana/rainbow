(ns rainbow.algorithms.proofs.ahof.quickselect-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.quickselect :as qsel]
            [rainbow.algorithms.reference.quickselect :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          qsel/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest quickselect-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (qsel/definition-ids checked-environment)
        theorems (qsel/theorem-ids checked-environment)]
    (is (= #{'quickselect/recurse-left?} (set (keys definitions))))
    (is (= #{'quickselect/target-in-left 'quickselect/left-target-below-pivot
             'quickselect/target-in-right}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-quickselect
  (is (true? (executable/recurse-left? 2 4)))
  (is (false? (executable/recurse-left? 7 4)))
  ;; 1st, 5th (median), 9th smallest of a shuffled list
  (let [xs [5 2 9 1 5 6 3 4 8]]
    (is (= 1 (executable/quickselect xs 1)))
    (is (= 5 (executable/quickselect xs 5)))
    (is (= 9 (executable/quickselect xs 9)))))
