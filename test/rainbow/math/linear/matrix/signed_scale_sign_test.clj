(ns rainbow.math.linear.matrix.signed-scale-sign-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.signed-scale-sign :as laws]))

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

(deftest finite-matrix-signed-scale-sign-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'signed/scale-difference-nonpositive-of-nonnegative-factor
             'signed/scale-difference-nonpositive-of-nonpositive-factor
             'signed/scale-difference-nonnegative-of-nonpositive-factor
             'vector/signed-scale-nonpositive-of-nonnegative-factor
             'vector/signed-scale-nonpositive-of-nonpositive-factor
             'vector/signed-scale-nonnegative-of-nonpositive-factor
             'matrix/signed-scale-nonpositive-of-nonnegative-factor
             'matrix/signed-scale-nonpositive-of-nonpositive-factor
             'matrix/signed-scale-nonnegative-of-nonpositive-factor}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
