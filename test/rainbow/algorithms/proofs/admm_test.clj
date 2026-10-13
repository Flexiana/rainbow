(ns rainbow.algorithms.proofs.admm-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.admm :as admm]
            [rainbow.algorithms.reference.admm :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          admm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest admm-dual-update-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (admm/definition-ids checked-environment)
        theorems (admm/theorem-ids checked-environment)]
    (is (= #{'admm/dual-update} (set (keys definitions))))
    (is (= #{'admm/dual-update-unfold
             'admm/residual-2d-example
             'admm/residual-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-admm-matches-the-recurrence
  ;; A residual accumulates onto a zero dual, and at consensus (x = z) the dual
  ;; variable is unchanged.
  (is (= [3 2] (executable/dual-update [0 0] [3 2] [0 0])))
  (is (= [1 1] (executable/dual-update [1 1] [5 5] [5 5])))
  (is (= [3 2] (first (executable/iterate-admm
                       (fn [_z _u] [3 2]) (fn [_x _u] [0 0])
                       [0 0] [0 0] [0 0] 1)))))
