(ns rainbow.math.linear.matrix.affine-nnrat-exact-rate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.affine-nnrat-exact-rate
             :as laws]))

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

(deftest finite-matrix-affine-nnrat-exact-rate-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{'signed/nnrat-power-scale} (set (keys definitions))))
    (is (= #{'signed/nnrat-power-scale-zero
             'signed/nnrat-power-scale-successor
             'signed/nnrat-power-scale-nonnegative
             'signed/nnrat-power-scale-monotone
             'matrix/affine-nnrat-row-sum-iterate-sup-distance-rate
             'matrix/affine-nnrat-successive-residual-rate
             'matrix/affine-nnrat-strong-row-iterate-error-exact-rate
             'matrix/affine-nnrat-strong-row-stopping-certificate-exact-rate}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
