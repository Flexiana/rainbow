(ns rainbow.algorithms.proofs.ahof.fisher-yates-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.fisher-yates :as fy]
            [rainbow.algorithms.reference.fisher-yates :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          fy/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fisher-yates-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (fy/definition-ids checked-environment)
        theorems (fy/theorem-ids checked-environment)]
    (is (= #{'fisher-yates/valid-swap?} (set (keys definitions))))
    (is (= #{'fisher-yates/in-range-swap-valid
             'fisher-yates/valid-swap-within-range
             'fisher-yates/out-of-range-swap-invalid}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-fisher-yates
  (is (true? (executable/valid-swap? 2 5)))
  (is (false? (executable/valid-swap? 7 5)))
  ;; any deterministic in-range rng yields a permutation of the input
  (let [shuffled (executable/shuffle-with [1 2 3 4 5] (fn [i] (mod (* i 7) (inc i))))]
    (is (executable/is-permutation? [1 2 3 4 5] shuffled))
    (is (= 5 (count shuffled)))))
