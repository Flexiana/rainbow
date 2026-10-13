(ns rainbow.math.linear.matrix.shape-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.shape :as shape]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (shape/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-matrix-shape-certificates-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (shape/definition-ids env)
        theorems (shape/theorem-ids env)]
    (is (= #{'matrix/compatible 'matrix/rectangular}
           (set (keys definitions))))
    (is (= #{'matrix/compatible-nil
             'matrix/compatible-cons
             'matrix/compatible-head-shape
             'matrix/compatible-tail
             'matrix/compatible-transport
             'matrix/rectangular-tail
             'matrix/compatible-with-head-of-rectangular}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
