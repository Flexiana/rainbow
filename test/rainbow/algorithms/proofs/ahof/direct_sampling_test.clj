(ns rainbow.algorithms.proofs.ahof.direct-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.direct-sampling :as ds]
            [rainbow.algorithms.reference.direct-sampling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ds/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest direct-sampling-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ds/definition-ids checked-environment)
        theorems (ds/theorem-ids checked-environment)]
    (is (= #{'direct-sampling/selects?} (set (keys definitions))))
    (is (= #{'direct-sampling/selects-category 'direct-sampling/selection-is-valid
             'direct-sampling/skips-below-draw}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-direct-sampling-inverse-transform
  (is (true? (executable/selects? 7 5)))
  (is (false? (executable/selects? 3 5)))
  ;; Distribution a:1/2, b:1/4, c:1/4; draw u=3/5 lands in b's interval.
  (is (= :b (executable/sample-categorical [[:a 1/2] [:b 1/4] [:c 1/4]] 3/5)))
  (is (= :a (executable/sample-categorical [[:a 1/2] [:b 1/4] [:c 1/4]] 1/4))))
