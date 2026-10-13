(ns rainbow.algorithms.proofs.factorial-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.factorial :as factorial]
            [rainbow.algorithms.reference.factorial :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          factorial/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest factorial-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (factorial/definition-ids checked-environment)
        theorems (factorial/theorem-ids checked-environment)]
    (is (= #{'factorial/fact} (set (keys definitions))))
    (is (= #{'factorial/fact-step-unfold 'factorial/fact-zero
             'factorial/fact-four 'factorial/fact-five}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-factorial-matches
  (is (= 1 (executable/fact 0)))
  (is (= 24 (executable/fact 4)))
  (is (= 120 (executable/fact 5)))
  (is (= 20 (executable/permutations 5 2)))
  (is (= 10 (executable/combinations 5 2))))
