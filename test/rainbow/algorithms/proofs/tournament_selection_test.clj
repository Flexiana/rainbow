(ns rainbow.algorithms.proofs.tournament-selection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.tournament-selection :as tournament]
            [rainbow.algorithms.reference.tournament-selection :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          tournament/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest tournament-selection-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (tournament/definition-ids checked-environment)
        theorems (tournament/theorem-ids checked-environment)]
    (is (= #{'tournament/nnrat-max 'tournament/winner}
           (set (keys definitions))))
    (is (= #{'tournament/max-keeps-larger
             'tournament/winner-example
             'tournament/winner-dominates-entrant}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-tournament-selection-picks-the-fittest
  (is (= 7 (executable/nnrat-max 2 7)))
  (is (= 7 (executable/nnrat-max 7 2)))
  (is (= 7 (executable/winner [3 7 2])))
  (is (= 0 (executable/winner [])))
  ;; Draw a 3-entry tournament from a population by index; the fittest wins.
  (is (= 9 (executable/tournament [3 9 1 5 7] [0 1 3])))
  ;; Winner dominates every entrant.
  (let [pop [3 7 2]]
    (is (every? #(<= % (executable/winner pop)) pop))))
