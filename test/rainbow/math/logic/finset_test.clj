(ns rainbow.math.logic.finset-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finite-powersets :as finite-powersets]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.finset :as finset]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finite-powersets/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-81 checkpoint rejected" {:checkpoint checkpoint})))
      (finset/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bundled-finset-definitions-are-reducible-axiom-free-proof-data
  (let [checked-environment @checked-environment
        ids (finset/definition-ids checked-environment)]
    (is (= #{'finset/Finset 'finset/to-set 'finset/finite-evidence
             'finset/empty 'finset/subset 'finset/nonempty
             'finset/singleton}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (kernel-checked? checked-environment id) (str name))))))

(deftest bundled-finset-theorem-profiles-are-exact
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
        classical-profile (conj extensional-profile excluded-middle)
        expected
        {'finset/subset-reflexive-explicit #{}
         'finset/subset-reflexive-implicit #{}
         'finset/empty-subset #{}
         'finset/empty-not-nonempty #{}
         'finset/empty-nonempty-proposition-equality
         #{proposition-extensionality}
         'finset/singleton-nonempty #{}
         'finset/nonempty-to-type #{}
         'finset/extensional extensional-profile
         'finset/eq-empty-or-nonempty classical-profile
         'finset/nonempty-not-equal-empty #{}
         'finset/nonempty-of-not-equal-empty classical-profile
         'finset/nonempty-equivalent-not-empty classical-profile
         'finset/is-empty-of-all-empty #{}
         'finset/singleton-injective #{}}
        ids (finset/theorem-ids checked-environment)]
    (is (= (set (keys expected)) (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (kernel-checked? checked-environment id) (str name))
        (is (= (get expected name) (kernel/axioms checked-environment id))
            (str name))))))
