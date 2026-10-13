(ns rainbow.math.finite.matrix-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.matrix :as matrix]
            [rainbow.algorithms.reference.finite-matrix :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (matrix/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-matrix-vector-laws-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (matrix/definition-ids env)
        theorems (matrix/theorem-ids env)]
    (is (= #{'matrix/vector-multiply} (set (keys definitions))))
    (is (= #{'matrix/vector-multiply-zero-like
             'matrix/vector-multiply-respects-equivalence
             'matrix/vector-multiply-additive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-finite-matrix-matches-row-dot-semantics
  (is (= [14 12]
         (executable/vector-multiply [[1 2] [3]] [4 5])))
  (is (= [24 24]
         (executable/vector-multiply [[1 2] [3 0]] [8 8]))))
