(ns rainbow.algorithms.proofs.ahof.rabin-karp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.rabin-karp :as rk]
            [rainbow.algorithms.reference.rabin-karp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rk/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rabin-karp-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rk/definition-ids checked-environment)
        theorems (rk/theorem-ids checked-environment)]
    (is (= #{'rabin-karp/candidate-match?} (set (keys definitions))))
    (is (= #{'rabin-karp/equal-hashes-candidate
             'rabin-karp/candidate-hashes-coincide
             'rabin-karp/unequal-hashes-mismatch}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-rabin-karp
  (is (true? (executable/candidate-match? 42 42)))
  (is (false? (executable/candidate-match? 17 42)))
  (is (= [0 9 12] (executable/search "AABAACAADAABAABA" "AAB")))
  (is (= [] (executable/search "abcabc" "xyz"))))
