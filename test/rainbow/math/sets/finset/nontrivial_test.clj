(ns rainbow.math.sets.finset.nontrivial-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finset-carriers :as finset-carriers]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.nontrivial :as finset-nontrivial]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finset-carriers/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-83 checkpoint rejected" {:checkpoint checkpoint})))
      (finset-nontrivial/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finset-nontrivial-is-a-reducible-set-view
  (let [checked-environment @checked-environment
        ids (finset-nontrivial/definition-ids checked-environment)
        id (get ids 'finset/nontrivial)
        declaration (environment/declaration checked-environment id)]
    (is (= #{'finset/nontrivial} (set (keys ids))))
    (is (= :definition (:rainbow/kind declaration)))
    (is (= :reducible (:rainbow/transparency declaration)))
    (is (= #{} (kernel/axioms checked-environment id)))
    (is (kernel-checked? checked-environment id))))

(deftest empty-and-singleton-nontrivial-profiles-are-exact
  (let [checked-environment @checked-environment
        proposition-extensionality
        (environment/resolve-id checked-environment
                                'logic/proposition-extensionality)
        expected
        {'finset/nontrivial-nonempty #{}
         'finset/empty-not-nontrivial #{}
         'finset/singleton-not-nontrivial #{}
         'finset/empty-nontrivial-proposition-equality
         #{proposition-extensionality}}
        ids (finset-nontrivial/theorem-ids checked-environment)]
    (is (= (set (keys expected)) (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (kernel-checked? checked-environment id) (str name))
        (is (= (get expected name) (kernel/axioms checked-environment id))
            (str name))))))
