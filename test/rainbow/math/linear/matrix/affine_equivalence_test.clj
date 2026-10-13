(ns rainbow.math.linear.matrix.affine-equivalence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.affine-equivalence :as laws]))

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

(deftest finite-matrix-affine-equivalence-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'matrix/affine-action-respects-offset-equivalence
             'matrix/affine-action-respects-values-equivalence
             'matrix/affine-action-respects-rows-equivalence
             'matrix/affine-action-respects-equivalence
             'matrix/affine-iterate-respects-initial-equivalence
             'matrix/affine-iterate-respects-equivalence
             'matrix/affine-iterate-fixed-point}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
