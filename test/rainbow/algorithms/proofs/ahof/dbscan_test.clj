(ns rainbow.algorithms.proofs.ahof.dbscan-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.dbscan :as dbscan]
            [rainbow.algorithms.reference.dbscan :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          dbscan/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest dbscan-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (dbscan/definition-ids checked-environment)
        theorems (dbscan/theorem-ids checked-environment)]
    (is (= #{'dbscan/is-core?} (set (keys definitions))))
    (is (= #{'dbscan/dense-point-is-core 'dbscan/core-meets-density
             'dbscan/sparse-point-not-core}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-dbscan
  (is (true? (executable/is-core? 5 3)))
  (is (false? (executable/is-core? 2 3)))
  ;; two dense clusters near 0-2 and 10-12, one noise point at 30
  (let [labels (executable/dbscan [0 1 2 10 11 12 30] 3/2 2)]
    (is (= (labels 0) (labels 1) (labels 2)))
    (is (= (labels 3) (labels 4) (labels 5)))
    (is (not= (labels 0) (labels 3)))
    (is (= -1 (labels 6)))))
