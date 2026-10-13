(ns rainbow.algorithms.proofs.ahof.christofides-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.christofides :as christofides]
            [rainbow.algorithms.reference.christofides :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          christofides/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest christofides-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (christofides/definition-ids checked-environment)
        theorems (christofides/theorem-ids checked-environment)]
    (is (= #{'christofides/within-bound?} (set (keys definitions))))
    (is (= #{'christofides/tour-within-guarantee 'christofides/tour-at-most-bound
             'christofides/tour-over-bound-rejected}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-christofides
  (is (true? (executable/within-bound? 13 15)))
  (is (false? (executable/within-bound? 17 15)))
  ;; 4 cities on a unit square (metric); optimal tour is 4, approximation within
  ;; the 3/2 bound (6)
  (let [dist [[0 1 2 1] [1 0 1 2] [2 1 0 1] [1 2 1 0]]]
    (is (true? (executable/certified-within-bound? dist 4)))
    (let [[tour cost] (executable/approximate-tour dist)]
      (is (= 0 (first tour)))
      (is (= 0 (last tour)))
      (is (<= cost 6)))))
