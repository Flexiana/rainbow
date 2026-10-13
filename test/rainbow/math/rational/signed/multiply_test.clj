(ns rainbow.math.rational.signed.multiply-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply :as signed-mul]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (signed-mul/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest signed-multiply-is-native-axiom-free
  (let [env @checked-environment
        definitions (signed-mul/definition-ids env)
        theorems (signed-mul/theorem-ids env)]
    (is (= #{'signed/multiply} (set (keys definitions))))
    (is (= #{'signed/multiply-unfold 'signed/multiply-two-times-three
             'signed/multiply-negative-two-times-three} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))
