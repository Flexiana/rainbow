(ns rainbow.math.finite.type-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.or-curriculum-first-mapping :as or-curriculum-first-mapping]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint or-curriculum-first-mapping/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-75 checkpoint rejected" {:checkpoint checkpoint})))
      (finite-type/extend-environment (:environment checkpoint)))))

(deftest finite-carrier-definitions-work-over-arbitrary-sorts
  (let [environment @checked-environment]
    (doseq [[name id] (finite-type/definition-ids environment)]
      (let [declaration (environment/declaration environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms environment id)) (str name))
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      #{'l})))
            (str name))))))

(deftest finite-carrier-bridges-have-explicit-minimal-axiom-profiles
  (let [environment @checked-environment
        ids (finite-type/theorem-ids environment)
        excluded-middle (environment/resolve-id environment
                                                'logic/excluded-middle)]
    (is (= 5 (count ids)))
    (is (= {#{} 3 #{excluded-middle} 2}
           (frequencies (map #(kernel/axioms environment %) (vals ids)))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration)))))
            (str name))))))
