(ns rainbow.algorithms.proofs.ahof.bin-packing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bin-packing :as bin]
            [rainbow.algorithms.reference.bin-packing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bin/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bin-packing-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bin/definition-ids checked-environment)
        theorems (bin/theorem-ids checked-environment)]
    (is (= #{'bin-packing/fits?} (set (keys definitions))))
    (is (= #{'bin-packing/item-fits 'bin-packing/placement-respects-capacity
             'bin-packing/oversized-opens-new-bin}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bin-packing
  (is (true? (executable/fits? 1/2 3/4)))
  (is (false? (executable/fits? 3/4 1/2)))
  ;; items [1/2 1/2 1/2] first-fit into 2 bins (first fills, third opens new)
  (is (= 2 (count (executable/first-fit [1/2 1/2 1/2])))))
