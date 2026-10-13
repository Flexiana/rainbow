(ns rainbow.math.finite.powerset-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.classical-infinitude-transport :as classical-infinitude-transport]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.powerset :as finite-powerset]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint classical-infinitude-transport/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-80 checkpoint rejected" {:checkpoint checkpoint})))
      (finite-powerset/extend-environment (:environment checkpoint)))))

(deftest list-powerset-is-reducible-axiom-free-proof-data
  (let [environment @checked-environment
        id (get (finite-powerset/definition-ids environment)
                'list/set-powerset)
        declaration (environment/declaration environment id)]
    (is (= :definition (:rainbow/kind declaration)))
    (is (= :reducible (:rainbow/transparency declaration)))
    (is (= #{} (kernel/axioms environment id)))
    (is (= :checked
           (:status (kernel/check environment
                                  (:rainbow/value declaration)
                                  (:rainbow/type declaration)
                                  (set (:rainbow/universes declaration))))))))

(deftest powerset-and-supremum-profiles-are-exact
  (let [environment @checked-environment
        excluded-middle
        (environment/resolve-id environment 'logic/excluded-middle)
        function-extensionality
        (environment/resolve-id environment 'logic/function-extensionality)
        proposition-extensionality
        (environment/resolve-id environment 'logic/proposition-extensionality)
        proof-irrelevance
        (environment/resolve-id environment 'logic/proof-irrelevance)
        powerset-profile
        #{excluded-middle function-extensionality proposition-extensionality}
        expected
        {'list/membership-set-powerset powerset-profile
         'set/finite-powerset powerset-profile
         'set/infinite-supremum powerset-profile
         'subtype/value-injective #{proof-irrelevance}}
        ids (finite-powerset/theorem-ids environment)]
    (is (= (set (keys expected)) (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration)))))
            (str name))
        (is (= (get expected name) (kernel/axioms environment id))
            (str name))))))
