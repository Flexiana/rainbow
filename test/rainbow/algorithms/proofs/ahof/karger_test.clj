(ns rainbow.algorithms.proofs.ahof.karger-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.karger :as karger]
            [rainbow.algorithms.reference.karger :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          karger/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest karger-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (karger/definition-ids checked-environment)
        theorems (karger/theorem-ids checked-environment)]
    (is (= #{'karger/keep-smaller-cut?} (set (keys definitions))))
    (is (= #{'karger/smaller-cut-kept 'karger/kept-cut-at-most-previous
             'karger/larger-cut-discarded}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-karger
  (is (true? (executable/keep-smaller-cut? 2 5)))
  (is (false? (executable/keep-smaller-cut? 7 5)))
  ;; two triangles joined by a single bridge -> min cut is 1
  (let [edges [[0 1] [1 2] [0 2] [2 3] [3 4] [4 5] [3 5]]]
    (is (= 1 (executable/min-cut 6 edges 40)))))
