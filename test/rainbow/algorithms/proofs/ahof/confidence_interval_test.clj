(ns rainbow.algorithms.proofs.ahof.confidence-interval-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.confidence-interval :as ci]
            [rainbow.algorithms.reference.confidence-interval :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ci/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest confidence-interval-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ci/definition-ids checked-environment)
        theorems (ci/theorem-ids checked-environment)]
    (is (= #{'confidence-interval/contains?} (set (keys definitions))))
    (is (= #{'confidence-interval/contains-interior-value
             'confidence-interval/excludes-value-above
             'confidence-interval/contained-meets-lower
             'confidence-interval/contained-meets-upper}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-confidence-interval
  (is (true? (executable/contains? 5 3 7)))
  (is (false? (executable/contains? 8 3 7)))
  ;; estimate 10, z 2, se 3/2 -> [7 13]
  (is (= [7 13] (executable/interval 10 2 3/2)))
  (is (true? (executable/covers? 10 2 3/2 12)))
  (is (false? (executable/covers? 10 2 3/2 20))))
