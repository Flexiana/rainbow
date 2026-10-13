(ns rainbow.math.nat.infinite-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finite-propositions-subtypes :as finite-propositions-subtypes]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.infinite :as nat-infinite]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finite-propositions-subtypes/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-77 checkpoint rejected" {:checkpoint checkpoint})))
      (nat-infinite/extend-environment (:environment checkpoint)))))

(deftest nat-infinitude-definitions-are-reducible-and-axiom-free
  (let [environment @checked-environment
        ids (nat-infinite/definition-ids environment)]
    (is (= 3 (count ids)))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms environment id)) (str name))
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration)))))
            (str name))))))

(deftest exact-nat-arithmetic-is-integrated-axiom-free
  (let [environment @checked-environment
        ids (nat-infinite/arithmetic-ids environment)]
    (is (= 3 (count ids)))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms environment id)) (str name)))))

(deftest nat-infinitude-theorems-are-kernel-checked-and-axiom-free
  (let [environment @checked-environment
        ids (nat-infinite/theorem-ids environment)]
    (is (= 7 (count ids)))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (= #{} (kernel/axioms environment id)) (str name))
        (is (= :checked
               (:status (kernel/check environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration)))))
            (str name))))))
