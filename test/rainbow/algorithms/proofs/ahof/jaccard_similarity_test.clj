(ns rainbow.algorithms.proofs.ahof.jaccard-similarity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.jaccard-similarity :as jaccard]
            [rainbow.algorithms.reference.jaccard-similarity :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          jaccard/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest jaccard-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (jaccard/definition-ids checked-environment)
        theorems (jaccard/theorem-ids checked-environment)]
    (is (= #{'jaccard/similarity} (set (keys definitions))))
    (is (= #{'jaccard/jaccard-example 'jaccard/identical-sets-similarity-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-jaccard
  (is (= 2/5 (executable/jaccard 2 5)))
  (is (= 1 (executable/jaccard 4 4)))
  ;; {1,2,3} vs {2,3,4}: intersection {2,3}=2, union {1,2,3,4}=4 -> 1/2
  (is (= 1/2 (executable/similarity #{1 2 3} #{2 3 4})))
  (is (= 0 (executable/similarity #{1 2} #{3 4}))))
