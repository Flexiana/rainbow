(ns rainbow.algorithms.proofs.ahof.kadane-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kadane :as kadane]
            [rainbow.algorithms.reference.kadane :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kadane/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kadane-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kadane/definition-ids checked-environment)
        theorems (kadane/theorem-ids checked-environment)]
    (is (= #{'kadane/extend?} (set (keys definitions))))
    (is (= #{'kadane/extending-helps 'kadane/extension-at-least-element
             'kadane/restart-when-not-helpful}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kadane
  (is (true? (executable/extend? 7 5)))
  (is (false? (executable/extend? 2 5)))
  ;; classic: [-2 1 -3 4 -1 2 1 -5 4] -> 6 (subarray [4 -1 2 1])
  (is (= 6 (executable/max-subarray [-2 1 -3 4 -1 2 1 -5 4])))
  (is (= 10 (executable/max-subarray [1 2 3 4]))))
