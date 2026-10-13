(ns rainbow.math.linear.matrix.linear-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.linear :as linear]
            [rainbow.algorithms.reference.finite-matrix :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (linear/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-matrix-linearity-is-native-and-axiom-free
  (let [env @checked-environment
        ids (linear/theorem-ids env)]
    (is (= #{'matrix/vector-multiply-output-shape
             'matrix/vector-multiply-negate
             'matrix/vector-multiply-scale}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-matrix-action-commutes-with-negation-and-scaling
  (let [rows [[1 2] [3 -1]]
        values [4 5]]
    (is (= (mapv - (executable/vector-multiply rows values))
           (executable/vector-multiply rows (mapv - values))))
    (is (= (mapv #(* 3 %) (executable/vector-multiply rows values))
           (executable/vector-multiply rows (mapv #(* 3 %) values))))))
