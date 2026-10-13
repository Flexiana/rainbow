(ns rainbow.math.linear.matrix.row-length-shape-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.row-length-shape :as row-length]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (row-length/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest row-length-shape-bridges-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (row-length/definition-ids env)
        theorems (row-length/theorem-ids env)]
    (is (= #{'vector/length 'matrix/row-length-compatible}
           (set (keys definitions))))
    (is (= #{'vector/length-equality-implies-same-shape
             'vector/same-shape-implies-length-equality
             'matrix/row-length-compatible-implies-compatible
             'matrix/compatible-implies-row-length-compatible
             'matrix/row-length-compatible-implies-rectangular
             'matrix/rectangular-implies-head-row-length-compatible}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
