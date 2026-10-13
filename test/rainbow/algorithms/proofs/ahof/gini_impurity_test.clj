(ns rainbow.algorithms.proofs.ahof.gini-impurity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gini-impurity :as gini]
            [rainbow.algorithms.reference.gini-impurity :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gini/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gini-impurity-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gini/definition-ids checked-environment)
        theorems (gini/theorem-ids checked-environment)]
    (is (= #{'gini-impurity/purer-split?} (set (keys definitions))))
    (is (= #{'gini-impurity/lower-impurity-preferred
             'gini-impurity/chosen-split-purer
             'gini-impurity/higher-impurity-not-preferred}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gini-impurity
  (is (true? (executable/purer-split? 1/4 1/2)))
  (is (false? (executable/purer-split? 1/2 1/4)))
  ;; pure node -> 0; 50/50 -> 1/2
  (is (= 0 (executable/gini [10 0])))
  (is (= 1/2 (executable/gini [5 5])))
  ;; a pure split beats a mixed one
  (is (= 1 (executable/best-split [[3 3] [4 0]]))))
