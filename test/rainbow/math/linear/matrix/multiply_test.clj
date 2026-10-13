(ns rainbow.math.linear.matrix.multiply-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.multiply :as laws]
            [rainbow.algorithms.reference.finite-matrix-multiply :as executable]))

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

(deftest finite-matrix-multiply-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{'matrix/multiply} (set (keys definitions))))
    (is (= #{'matrix/multiply-empty-left
             'matrix/multiply-cons-left
             'matrix/multiply-respects-left-equivalence
             'matrix/multiply-respects-right-equivalence
             'matrix/multiply-respects-equivalence}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-matrix-multiply-is-exact-and-total
  (is (= [] (executable/multiply [] [[1 2] [3 4]])))
  (is (= [[19 22] [43 50]]
         (executable/multiply [[1 2] [3 4]]
                              [[5 6] [7 8]])))
  (is (= [[1/2 1/3]]
         (executable/multiply [[1]] [[1/2 1/3]])))
  (is (= [[11 14]]
         (executable/multiply [[1 2 99]] [[3 4] [4 5]]))))
