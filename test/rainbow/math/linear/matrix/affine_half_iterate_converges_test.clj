(ns rainbow.math.linear.matrix.affine-half-iterate-converges-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.affine-half-iterate-converges
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

(deftest finite-matrix-affine-half-iterate-converges-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)
        declarations (concat definitions theorems)]
    (is (= #{'analysis/signed-rate-null} (set (keys definitions))))
    (is (= #{'analysis/signed-half-power-one-rate-null
             'analysis/signed-rate-null-dominated
             'analysis/signed-rate-null-respects-equivalence
             'analysis/signed-half-power-rate-null-of-at-most-one
             'matrix/affine-half-iterate-sup-distance-rate-null
             'matrix/affine-half-iterate-converges-to-fixed-point}
           (set (keys theorems))))
    (doseq [[name id] declarations]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
