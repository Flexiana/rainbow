(ns rainbow.math.rational.signed.order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.order :as signed-order]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d61-q-learning/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D61 checkpoint rejected" {:checkpoint checkpoint})))
      (signed-order/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-order-and-structural-laws-are-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (signed-order/definition-ids checked-environment)
        theorems (signed-order/theorem-ids checked-environment)]
    (is (= #{'signed/at-most} (set (keys definitions))))
    (is (= #{'signed/at-most-reflexive 'signed/negate-involutive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
