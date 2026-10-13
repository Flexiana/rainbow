(ns rainbow.algorithms.proofs.ahof.cross-entropy-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.cross-entropy :as cross-entropy]
            [rainbow.algorithms.reference.cross-entropy :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          cross-entropy/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest cross-entropy-elite-selection-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (cross-entropy/definition-ids checked-environment)
        theorems (cross-entropy/theorem-ids checked-environment)]
    (is (= #{'cross-entropy/elite?} (set (keys definitions))))
    (is (= #{'cross-entropy/selects-elite
             'cross-entropy/elite-meets-threshold
             'cross-entropy/excludes-non-elite}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-cross-entropy-selects-elite
  (is (true? (executable/elite? 7 5)))
  (is (false? (executable/elite? 3 5)))
  ;; Top-half elite of a scored population.
  (let [scored [[:a 1] [:b 9] [:c 4] [:d 7]]
        elite (executable/elite-set scored 1/2)]
    (is (= #{:b :d} (set (map first elite))))))
