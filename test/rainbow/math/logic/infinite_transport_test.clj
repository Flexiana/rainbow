(ns rainbow.math.logic.infinite-transport-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.nat-infinitude :as nat-infinitude]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.infinite-transport :as infinite-transport]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint nat-infinitude/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-78 checkpoint rejected" {:checkpoint checkpoint})))
      (infinite-transport/extend-environment (:environment checkpoint)))))

(deftest native-int-is-a-kernel-validated-two-constructor-inductive
  (let [environment @checked-environment
        ids (infinite-transport/inductive-ids environment)]
    (is (= 4 (count ids)))
    (is (= #{:inductive :constructor :recursor}
           (set (map #(get-in environment
                              [:rainbow.environment/declarations %
                               :rainbow/kind])
                     (vals ids)))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms environment id)) (str name)))))

(deftest int-projection-is-reducible-and-axiom-free
  (let [environment @checked-environment]
    (doseq [[name id] (infinite-transport/definition-ids environment)]
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

(deftest sort-polymorphic-transport-and-int-infinitude-are-axiom-free
  (let [environment @checked-environment
        ids (infinite-transport/theorem-ids environment)]
    (is (= 5 (count ids)))
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
