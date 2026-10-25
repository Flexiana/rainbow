(ns rainbow.math.finite.subtype-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finite-carriers :as finite-carriers]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.subtype :as finite-subtype]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finite-carriers/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-76 checkpoint rejected" {:checkpoint checkpoint})))
      (finite-subtype/extend-environment (:environment checkpoint)))))

(deftest finite-subtype-support-has-explicit-axiom-profiles
  (let [environment @checked-environment
        ids (finite-subtype/theorem-ids environment)
        excluded-middle
        (environment/resolve-id environment 'logic/excluded-middle)
        proof-irrelevance
        (environment/resolve-id environment 'logic/proof-irrelevance)
        proposition-extensionality
        (environment/resolve-id environment 'logic/proposition-extensionality)
        expected
        {'type/finite-of-subsingleton #{excluded-middle}
         'subtype/extensional #{proof-irrelevance}
         'set/finite-subtype-equivalence
         #{excluded-middle proof-irrelevance}
         'set/finite-subtype-proposition-equality
         #{excluded-middle proof-irrelevance proposition-extensionality}}]
    (is (= 4 (count ids)))
    (let [definition-id
          (get (finite-subtype/definition-ids environment)
               'type/subsingleton)
          declaration (environment/declaration environment definition-id)]
      (is (= :definition (:rainbow/kind declaration)))
      (is (= :reducible (:rainbow/transparency declaration)))
      (is (= #{} (kernel/axioms environment definition-id))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)]
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration)))))
            (str name))
        (is (= (get expected name) (kernel/axioms environment id))
            (str name))))))
