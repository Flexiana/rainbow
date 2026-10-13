(ns rainbow.algorithms.proofs.ahof.johnson-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.johnson :as johnson]
            [rainbow.algorithms.reference.johnson :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          johnson/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest johnson-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (johnson/definition-ids checked-environment)
        theorems (johnson/theorem-ids checked-environment)]
    (is (= #{'johnson/nonneg-reweighted?} (set (keys definitions))))
    (is (= #{'johnson/reweighted-edge-nonneg 'johnson/valid-reweight-at-least-zero
             'johnson/zero-reweight-usable}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-johnson
  (is (true? (executable/nonneg-reweighted? 4)))
  (is (false? (executable/nonneg-reweighted? -1)))
  ;; path 0->1 (4), 1->2 (3), 0->2 (10): all-pairs distances
  (let [d (executable/all-pairs 3 [[0 1 4] [1 2 3] [0 2 10]])]
    (is (= 0 ((d 0) 0)))
    (is (= 4 ((d 0) 1)))
    (is (= 7 ((d 0) 2)))
    (is (= 3 ((d 1) 2)))))
