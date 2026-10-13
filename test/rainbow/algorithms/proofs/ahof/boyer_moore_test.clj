(ns rainbow.algorithms.proofs.ahof.boyer-moore-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.boyer-moore :as bm]
            [rainbow.algorithms.reference.boyer-moore :as executable]))

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

(deftest boyer-moore-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bm/definition-ids checked-environment)
        theorems (bm/theorem-ids checked-environment)]
    (is (= #{'boyer-moore/is-majority?} (set (keys definitions))))
    (is (= #{'boyer-moore/confirmed-majority 'boyer-moore/majority-meets-threshold
             'boyer-moore/no-majority}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-boyer-moore
  (is (true? (executable/is-majority? 4 4)))
  (is (false? (executable/is-majority? 3 4)))
  ;; 3 appears 4 of 7 times -> majority
  (is (= 3 (executable/majority-element [3 3 4 2 3 3 5])))
  ;; no element exceeds n/2
  (is (nil? (executable/majority-element [1 2 3 4]))))
