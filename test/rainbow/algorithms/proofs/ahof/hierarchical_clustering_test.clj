(ns rainbow.algorithms.proofs.ahof.hierarchical-clustering-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.hierarchical-clustering :as hc]
            [rainbow.algorithms.reference.hierarchical-clustering :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          hc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hierarchical-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hc/definition-ids checked-environment)
        theorems (hc/theorem-ids checked-environment)]
    (is (= #{'hierarchical/closest-pair} (set (keys definitions))))
    (is (= #{'hierarchical/merges-closest-pair
             'hierarchical/merges-second-when-closer
             'hierarchical/merged-is-closest}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hierarchical
  (is (= 0 (executable/closest-pair 2 0 6 1)))
  (is (= 1 (executable/closest-pair 9 0 4 1)))
  ;; points 0,1,10,11: first merges are the close pairs (dist 1)
  (let [merges (executable/cluster [0 1 10 11])]
    (is (= 3 (count merges)))
    (is (= 1 (nth (first merges) 2)))))
