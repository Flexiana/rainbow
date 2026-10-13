(ns rainbow.algorithms.proofs.ahof.conformal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.conformal :as conformal]
            [rainbow.algorithms.reference.conformal :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          conformal/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest conformal-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (conformal/definition-ids checked-environment)
        theorems (conformal/theorem-ids checked-environment)]
    (is (= #{'conformal/in-prediction-set?} (set (keys definitions))))
    (is (= #{'conformal/includes-conforming 'conformal/included-within-threshold
             'conformal/excludes-nonconforming}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-conformal-predicts
  (is (true? (executable/in-prediction-set? 3 5)))
  (is (false? (executable/in-prediction-set? 7 5)))
  ;; threshold for scores [1 2 3 4] at alpha=1/4: ceil(5*3/4)=4 -> 4th smallest = 4
  (is (= 4 (executable/empirical-quantile [4 1 3 2] 1/4)))
  (is (= #{:a :b} (executable/prediction-set {:a 3 :b 4 :c 9} [:a :b :c] 5))))
