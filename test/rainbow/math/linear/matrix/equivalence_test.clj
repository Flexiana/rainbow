(ns rainbow.math.linear.matrix.equivalence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.equivalence :as equivalence]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (equivalence/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-matrix-equivalence-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (equivalence/definition-ids env)
        theorems (equivalence/theorem-ids env)]
    (is (= #{'matrix/equivalent} (set (keys definitions))))
    (is (= #{'matrix/equivalent-reflexive
             'matrix/equivalent-symmetric
             'matrix/vector-multiply-respects-matrix-equivalence
             'matrix/vector-multiply-respects-both-equivalences}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
