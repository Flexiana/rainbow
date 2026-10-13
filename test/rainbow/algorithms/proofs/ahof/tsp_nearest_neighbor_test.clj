(ns rainbow.algorithms.proofs.ahof.tsp-nearest-neighbor-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.tsp-nearest-neighbor :as tsp]
            [rainbow.algorithms.reference.tsp-nearest-neighbor :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          tsp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest tsp-nn-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (tsp/definition-ids checked-environment)
        theorems (tsp/theorem-ids checked-environment)]
    (is (= #{'tsp-nn/nearer-city} (set (keys definitions))))
    (is (= #{'tsp-nn/visits-nearest 'tsp-nn/visits-second-when-nearer
             'tsp-nn/visited-is-nearest}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-tsp-nn
  (is (= 2 (executable/nearer-city 3 2 8 5)))
  (is (= 5 (executable/nearer-city 9 2 4 5)))
  ;; 4 cities in a line 0-1-2-3: NN from 0 visits 0 1 2 3 then back
  (let [[path total] (executable/tour [[0 1 2 3] [1 0 1 2] [2 1 0 1] [3 2 1 0]])]
    (is (= [0 1 2 3 0] path))
    (is (= 6 total))))
