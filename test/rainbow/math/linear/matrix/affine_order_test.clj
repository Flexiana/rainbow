(ns rainbow.math.linear.matrix.affine-order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.affine-order :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)
        r (kernel/check env (:rainbow/value d) (:rainbow/type d)
                        (set (:rainbow/universes d)))]
    (= :checked (:status r))))

(deftest finite-matrix-affine-order-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)
        declarations (merge definitions theorems)]
    (is (= #{'matrix/affine-action} (set (keys definitions))))
    (is (= #{'matrix/affine-action-unfold
             'matrix/affine-action-monotone-values
             'matrix/affine-action-antitone-values
             'matrix/affine-action-monotone-rows
             'matrix/affine-action-antitone-rows
             'matrix/affine-action-monotone-offset
             'matrix/affine-action-monotone-offset-values
             'matrix/affine-action-monotone-offset-rows
             'matrix/affine-action-monotone
             'matrix/affine-action-antitone
             'matrix/affine-action-monotone-all
             'matrix/affine-action-bounds-offset
             'matrix/affine-action-bounds-nonnegative-rows
             'matrix/affine-action-bounds-nonpositive-rows
             'matrix/affine-action-bounds-nonnegative-values
             'matrix/affine-action-bounds-nonpositive-values}
           (set (keys theorems))))
    (doseq [[name id] declarations]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
