(ns rainbow.algorithms.proofs.ahof.manacher-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.manacher :as manacher]
            [rainbow.algorithms.reference.manacher :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          manacher/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest manacher-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (manacher/definition-ids checked-environment)
        theorems (manacher/theorem-ids checked-environment)]
    (is (= #{'manacher/characters-match?} (set (keys definitions))))
    (is (= #{'manacher/equal-chars-extend 'manacher/matching-chars-coincide
             'manacher/different-chars-stop}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-manacher
  (is (true? (executable/characters-match? \A \A)))
  (is (false? (executable/characters-match? \A \B)))
  (is (= "bab" (executable/longest-palindrome "babad")))
  (is (= "cbbc" (executable/longest-palindrome "acbbcd")))
  (is (= "a" (executable/longest-palindrome "abc"))))
