(ns rainbow.algorithms.proofs.ahof.concrete-reachability-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.concrete-reachability :as reachability]
            [rainbow.algorithms.reference.concrete-reachability :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          reachability/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest concrete-reachability-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (reachability/definition-ids checked-environment)
        theorems (reachability/theorem-ids checked-environment)]
    (is (= #{'reachability/reach-step} (set (keys definitions))))
    (is (= #{'reachability/reach-step-cons
             'reachability/reach-step-example
             'reachability/reach-step-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-concrete-reachability-traces-forward-image
  (is (= [2 3 4] (executable/reach-step inc [1 2 3])))
  (is (= [] (executable/reach-step inc [])))
  ;; Two steps of the +1 dynamics from {0}: {0} -> {1} -> {2}.
  (is (= [2] (executable/reachable inc [0] 2))))
