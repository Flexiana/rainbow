(ns rainbow.algorithms.proofs.ahof.sac-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.sac :as sac]
            [rainbow.algorithms.reference.sac :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sac/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest sac-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sac/definition-ids checked-environment)
        theorems (sac/theorem-ids checked-environment)]
    (is (= #{'sac/soft-value} (set (keys definitions))))
    (is (= #{'sac/soft-value-example 'sac/collapses-to-reward}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-sac-soft-value
  (is (= 3/2 (executable/soft-value 1 1/2 1)))
  (is (= 2 (executable/soft-value 2 0 5)))
  ;; soft Q target: r=1, gamma=1/2, V'=1, alpha=1/2, H'=1 -> 1 + 1/2*(1+1/2) = 7/4
  (is (= 7/4 (executable/soft-q-target 1 1/2 1 1/2 1))))
