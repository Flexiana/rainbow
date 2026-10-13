(ns rainbow.algorithms.proofs.list-maximum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.list-maximum :as list-maximum]
            [rainbow.algorithms.reference.list-maximum :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          list-maximum/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest list-maximum-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (list-maximum/definition-ids checked-environment)
        theorems (list-maximum/theorem-ids checked-environment)]
    (is (= #{'list-maximum/nnrat-max 'list-maximum/maximum}
           (set (keys definitions))))
    (is (= #{'list-maximum/nnrat-max-example 'list-maximum/maximum-empty
             'list-maximum/maximum-cons 'list-maximum/maximum-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-list-maximum-reduces
  (is (= 7 (executable/list-maximum [3 7 2])))
  (is (= 0 (executable/list-maximum [])))
  (is (= 7 (executable/nnrat-max 3 7)))
  (is (= 9 (executable/list-maximum [1 9 4 2]))))
