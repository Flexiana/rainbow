(ns rainbow.math.sets.finset.powerset-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finset-nontrivial :as finset-nontrivial]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.powerset :as finset-powerset]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finset-nontrivial/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-84 checkpoint rejected" {:checkpoint checkpoint})))
      (finset-powerset/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest powerset-is-reducible-native-finset-data
  (let [checked-environment @checked-environment
        ids (finset-powerset/definition-ids checked-environment)
        id (get ids 'finset/powerset)
        declaration (environment/declaration checked-environment id)
        expected-profile
        (set (map #(environment/resolve-id checked-environment %)
                  ['logic/excluded-middle
                   'logic/function-extensionality
                   'logic/proposition-extensionality
                   'logic/proof-irrelevance]))]
    (is (= #{'finset/powerset} (set (keys ids))))
    (is (= :definition (:rainbow/kind declaration)))
    (is (= :reducible (:rainbow/transparency declaration)))
    (is (= expected-profile (kernel/axioms checked-environment id)))
    (is (kernel-checked? checked-environment id))))

(deftest powerset-laws-have-exact-profiles
  (let [checked-environment @checked-environment
        profile
        (set (map #(environment/resolve-id checked-environment %)
                  ['logic/excluded-middle
                   'logic/function-extensionality
                   'logic/proposition-extensionality
                   'logic/proof-irrelevance]))
        ids (finset-powerset/theorem-ids checked-environment)]
    (is (= #{'finset/member-powerset-equivalent-subset
             'finset/self-member-powerset
             'finset/powerset-monotone
             'finset/powerset-nonempty
             'finset/powerset-injective}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (kernel-checked? checked-environment id) (str name))
      (is (= profile (kernel/axioms checked-environment id)) (str name)))))
