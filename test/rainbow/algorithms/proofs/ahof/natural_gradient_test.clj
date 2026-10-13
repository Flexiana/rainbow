(ns rainbow.algorithms.proofs.ahof.natural-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.natural-gradient :as natural-gradient]
            [rainbow.algorithms.reference.natural-gradient :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          natural-gradient/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest natural-gradient-update-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (natural-gradient/definition-ids checked-environment)
        theorems (natural-gradient/theorem-ids checked-environment)]
    (is (= #{'natural-gradient/update} (set (keys definitions))))
    (is (= #{'natural-gradient/update-unfold
             'natural-gradient/update-unit-2d-example
             'natural-gradient/update-unit-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-natural-gradient-updates
  (is (= [3 2] (executable/update-step [0 0] 1 [3 2])))
  ;; Preconditioning by a diagonal inverse-Fisher scales each gradient component.
  (is (= [6 1] (executable/precondition (fn [[g1 g2]] [(* 2 g1) (* 1/2 g2)])
                                        [3 2]))))
