(ns rainbow.algorithms.proofs.ahof.held-karp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.held-karp :as hk]
            [rainbow.algorithms.reference.held-karp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          hk/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest held-karp-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hk/definition-ids checked-environment)
        theorems (hk/theorem-ids checked-environment)]
    (is (= #{'held-karp/path-cost 'held-karp/better} (set (keys definitions))))
    (is (= #{'held-karp/path-cost-example 'held-karp/takes-cheaper-predecessor
             'held-karp/chosen-subpath-minimal}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-held-karp
  (is (= 7 (executable/path-cost 3 4)))
  (is (= 6 (executable/better 9 6)))
  ;; 4-city symmetric TSP; optimal tour cost 80
  (is (= 80 (executable/tsp [[0 10 15 20] [10 0 35 25] [15 35 0 30] [20 25 30 0]]))))
