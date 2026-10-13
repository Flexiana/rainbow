(ns rainbow.algorithms.proofs.nearest-neighbor-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.nearest-neighbor :as ahof-d25]
            [rainbow.algorithms.proofs.nearest-neighbor :as iteration]
            [rainbow.algorithms.reference.nearest-neighbor :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/v5-composite-metric/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "V5 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d25/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nearest-neighbor-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'decision/nearest-value} (set (keys definitions))))
    (is (= #{'decision/nearest-value-unfold} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d25-nearest-neighbor-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d25/theorem-ids checked-environment)]
    (is (= #{'ahof-d25/query-near-a-is-value-a
             'ahof-d25/query-near-b-is-value-b
             'ahof-d25/nearest-neighbor}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-nearest-neighbor-follows-the-nearer-point
  ;; Data points with values 3/4 and 1/4. A query at distances (1/4, 1/2) is
  ;; nearer the first, approximating to 3/4; a query at distances (1/2, 1/4) is
  ;; nearer the second, approximating to 1/4.
  (is (= 3/4 (executable/nearest-value 1/4 3/4 1/2 1/4)))
  (is (= 1/4 (executable/nearest-value 1/2 3/4 1/4 1/4)))
  ;; Ties keep the first point.
  (is (= 3/4 (executable/nearest-value 1/3 3/4 1/3 1/4))))
