(ns rainbow.algorithms.proofs.ahof.mesh-adaptive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.mesh-adaptive :as mads]
            [rainbow.algorithms.reference.mesh-adaptive :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          mads/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest mads-poll-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mads/definition-ids checked-environment)
        theorems (mads/theorem-ids checked-environment)]
    (is (= #{'mads/poll} (set (keys definitions))))
    (is (= #{'mads/poll-unfold
             'mads/poll-unit-2d-example
             'mads/poll-unit-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-mads-polls-and-adapts
  (is (= [3 2] (executable/poll [0 0] 1 [3 2])))
  ;; Minimizing (x-3)^2: from x=0 a +1 poll improves, so the incumbent advances
  ;; and the mesh coarsens.
  (let [objective (fn [[x]] (* (- x 3) (- x 3)))
        [x* delta*] (executable/poll-and-adapt objective [0] 1 [[1] [-1]])]
    (is (= [1] x*))
    (is (= 2 delta*))))
