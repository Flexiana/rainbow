(ns rainbow.algorithms.proofs.ahof.binary-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.binary-search :as bs]
            [rainbow.algorithms.reference.binary-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest binary-search-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bs/definition-ids checked-environment)
        theorems (bs/theorem-ids checked-environment)]
    (is (= #{'binary-search/search-left?} (set (keys definitions))))
    (is (= #{'binary-search/small-target-searches-left
             'binary-search/left-branch-sound
             'binary-search/large-target-searches-right}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-binary-search
  (is (true? (executable/search-left? 3 5)))
  (is (false? (executable/search-left? 8 5)))
  (is (= 3 (executable/binary-search [1 3 5 7 9 11] 7)))
  (is (= 0 (executable/binary-search [1 3 5 7 9 11] 1)))
  (is (nil? (executable/binary-search [1 3 5 7 9 11] 4))))
