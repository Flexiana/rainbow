(ns rainbow.math.linear.matrix.affine-strong-row-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.affine-strong-row-contraction
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

(deftest finite-matrix-affine-strong-row-contraction-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'signed/zero-at-most-from-nnrat
             'matrix/nnrat-row-sums-imply-half-bound
             'matrix/affine-nnrat-strong-row-fixed-points-have-zero-sup-distance
             'matrix/affine-nnrat-strong-row-fixed-points-unique
             'matrix/affine-nnrat-strong-row-iterate-sup-distance-rate
             'matrix/affine-nnrat-strong-row-iterate-sup-distance-rate-null
             'matrix/affine-nnrat-strong-row-iterate-converges-to-fixed-point}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
