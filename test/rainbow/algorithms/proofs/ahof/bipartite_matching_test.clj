(ns rainbow.algorithms.proofs.ahof.bipartite-matching-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bipartite-matching :as bm]
            [rainbow.algorithms.reference.bipartite-matching :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bipartite-matching-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bm/definition-ids checked-environment)
        theorems (bm/theorem-ids checked-environment)]
    (is (= #{'bipartite-matching/can-match?} (set (keys definitions))))
    (is (= #{'bipartite-matching/free-neighbor-matchable
             'bipartite-matching/reassignable-partner-matchable
             'bipartite-matching/taken-stuck-partner-fails}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bipartite-matching
  (is (true? (executable/can-match? true false)))
  (is (true? (executable/can-match? false true)))
  (is (false? (executable/can-match? false false)))
  ;; lefts {0 1 2} to rights via adj; a perfect matching of size 3 exists
  (is (= 3 (executable/max-matching [0 1 2] {0 #{:a :b} 1 #{:a} 2 #{:b :c}})))
  ;; a bottleneck limits the matching to 1 (both lefts want only :a)
  (is (= 1 (executable/max-matching [0 1] {0 #{:a} 1 #{:a}}))))
