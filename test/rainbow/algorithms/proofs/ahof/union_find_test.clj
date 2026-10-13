(ns rainbow.algorithms.proofs.ahof.union-find-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.union-find :as uf]
            [rainbow.algorithms.reference.union-find :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          uf/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest union-find-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (uf/definition-ids checked-environment)
        theorems (uf/theorem-ids checked-environment)]
    (is (= #{'union-find/connected?} (set (keys definitions))))
    (is (= #{'union-find/same-representative-connected
             'union-find/different-representative-disconnected
             'union-find/connected-implies-le}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-union-find
  (is (true? (executable/connected? 3 3)))
  (is (false? (executable/connected? 3 5)))
  (let [parent {0 0, 1 0, 2 1, 3 3}]
    (is (= 0 (executable/find-rep parent 2)))
    (is (= 3 (executable/find-rep parent 3)))))
