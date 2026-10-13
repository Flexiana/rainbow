(ns rainbow.math.linear.matrix.signed-scale-subtract-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.signed-scale-subtract :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-matrix-signed-scale-subtract-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'signed/multiply-subtract-left
             'signed/multiply-subtract-right
             'signed/scale-difference-negate-factor
             'signed/scale-difference-negate-value
             'signed/scale-difference-subtract-factor
             'signed/scale-difference-subtract-value
             'vector/signed-scale-negate-factor
             'vector/signed-scale-negate-value
             'vector/signed-scale-subtract-factor
             'vector/signed-scale-subtract-value
             'matrix/signed-scale-negate-factor
             'matrix/signed-scale-negate-value
             'matrix/signed-scale-subtract-factor
             'matrix/signed-scale-subtract-value}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
