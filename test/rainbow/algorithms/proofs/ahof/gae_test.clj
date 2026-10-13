(ns rainbow.algorithms.proofs.ahof.gae-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gae :as gae]
            [rainbow.algorithms.reference.gae :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gae/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gae-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gae/definition-ids checked-environment)
        theorems (gae/theorem-ids checked-environment)]
    (is (= #{'gae/gae2} (set (keys definitions))))
    (is (= #{'gae/gae2-example 'gae/collapses-to-td} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gae-combines
  (is (= 3/2 (executable/gae2 1 1 1/2)))
  (is (= 2 (executable/gae2 2 5 0)))
  ;; general GAE over [1 1 1] with w=1/2: 1 + 1/2 + 1/4 = 7/4
  (is (= 7/4 (executable/gae [1 1 1] 1/2))))
