(ns rainbow.algorithms.proofs.ahof.kmp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kmp :as kmp]
            [rainbow.algorithms.reference.kmp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kmp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kmp-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kmp/definition-ids checked-environment)
        theorems (kmp/theorem-ids checked-environment)]
    (is (= #{'kmp/matched?} (set (keys definitions))))
    (is (= #{'kmp/full-match-reports 'kmp/occurrence-matched-whole-pattern
             'kmp/partial-match-not-occurrence}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kmp
  (is (true? (executable/matched? 4 4)))
  (is (false? (executable/matched? 2 4)))
  (is (= [0 10 15] (executable/search "ABABDABACDABABCABAB" "ABAB")))
  (is (= [] (executable/search "abcde" "xyz"))))
