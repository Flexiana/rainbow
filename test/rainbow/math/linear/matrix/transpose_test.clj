(ns rainbow.math.linear.matrix.transpose-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.transpose :as transpose-laws]
            [rainbow.algorithms.reference.finite-matrix-transpose :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (transpose-laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-matrix-transpose-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (transpose-laws/definition-ids env)
        theorems (transpose-laws/theorem-ids env)]
    (is (= #{'matrix/prepend-column 'matrix/transpose}
           (set (keys definitions))))
    (is (= #{'matrix/prepend-column-empty-vector
             'matrix/prepend-column-cons-empty
             'matrix/prepend-column-cons-cons
             'matrix/transpose-empty
             'matrix/transpose-cons}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-transpose-matches-total-row-major-semantics
  (is (= [] (executable/transpose [])))
  (is (= [[1] [2] [3]]
         (executable/transpose [[1 2 3]])))
  (is (= [[1 4] [2 5] [3 6]]
         (executable/transpose [[1 2 3] [4 5 6]])))
  (is (= [[1 3] [2]]
         (executable/transpose [[1 2] [3]])))
  (is (= [[1 2]]
         (executable/transpose [[1] [2 3]])))
  (is (= [[1 3] [2 4]]
         (executable/prepend-column [1 2] [[3] [4] [5]]))))
