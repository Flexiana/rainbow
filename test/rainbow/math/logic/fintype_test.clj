(ns rainbow.math.logic.fintype-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finset-extensional :as finset-extensional]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.fintype :as fintype]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finset-extensional/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-82 checkpoint rejected" {:checkpoint checkpoint})))
      (fintype/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fintype-definitions-are-reducible-axiom-free-proof-data
  (let [checked-environment @checked-environment
        ids (fintype/definition-ids checked-environment)]
    (is (= #{'fintype/Fintype 'fintype/elements 'fintype/complete}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (kernel-checked? checked-environment id) (str name))))))

(deftest fintype-theorem-profiles-are-exact
  (let [checked-environment @checked-environment
        excluded-middle
        (environment/resolve-id checked-environment 'logic/excluded-middle)
        proof-irrelevance
        (environment/resolve-id checked-environment 'logic/proof-irrelevance)
        function-extensionality
        (environment/resolve-id checked-environment 'logic/function-extensionality)
        proposition-extensionality
        (environment/resolve-id checked-environment
                                'logic/proposition-extensionality)
        extensional-profile
        #{proof-irrelevance function-extensionality proposition-extensionality}
        finite-subtype-profile #{proof-irrelevance excluded-middle}
        expected
        {'fintype/from-finite #{}
         'fintype/to-finite #{}
         'fintype/subsingleton extensional-profile
         'fintype/finite-equivalent-nonempty #{}
         'fintype/is-empty-equivalent-infinite #{}
         'fintype/infinite-of-is-empty #{}
         'fintype/is-empty-proposition-equality
         #{proposition-extensionality}
         'set/finite-to-nonempty-fintype finite-subtype-profile
         'set/universal-finite-equivalent-nonempty-fintype #{}
         'set/finite-equivalent-subtype-fintype finite-subtype-profile}
        ids (fintype/theorem-ids checked-environment)]
    (is (= (set (keys expected)) (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (kernel-checked? checked-environment id) (str name))
        (is (= (get expected name) (kernel/axioms checked-environment id))
            (str name))))))
