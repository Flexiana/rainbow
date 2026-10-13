(ns rainbow.algorithms.proofs.penalty-method-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.penalty-method :as penalty]
            [rainbow.algorithms.reference.penalty-method :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (penalty/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest penalty-augmented-objective-is-native-axiom-free
  (let [env @checked-environment
        definitions (penalty/definition-ids env)
        theorems (penalty/theorem-ids env)]
    (is (= #{'penalty/augmented} (set (keys definitions))))
    (is (= #{'penalty/augmented-unfold 'penalty/infeasible-example
             'penalty/feasible-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-penalty-augments-objective-exactly
  ;; Infeasible: 1 + 2*3 = 7.
  (is (= 7 (executable/augmented 1 2 3)))
  ;; Feasible (penalty 0): augmented equals the objective.
  (is (= 5 (executable/augmented 5 2 0)))
  ;; The one-sided penalty is zero when feasible and positive when violated.
  (is (= 0 (executable/violation -3)))
  (is (= 4 (executable/violation 2)))
  ;; A full augmented objective with the squared-violation penalty.
  (is (= 13 (executable/augmented 1 3 (executable/violation 2)))))
