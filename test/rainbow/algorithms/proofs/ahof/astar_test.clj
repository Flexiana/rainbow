(ns rainbow.algorithms.proofs.ahof.astar-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.astar :as astar]
            [rainbow.algorithms.reference.astar :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          astar/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest astar-f-value-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (astar/definition-ids checked-environment)
        theorems (astar/theorem-ids checked-environment)]
    (is (= #{'astar/f-value} (set (keys definitions))))
    (is (= #{'astar/f-value-unfold
             'astar/f-value-example
             'astar/admissibility-bound}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-astar-finds-optimal-path
  (is (= 7 (executable/f-value 3 4)))
  ;; Graph S->A(1) S->B(4) A->G(5) B->G(1): optimal S->B->G = 5 (not S->A->G = 6).
  (let [succ {:S [[:A 1] [:B 4]] :A [[:G 5]] :B [[:G 1]] :G []}
        cost (executable/search :S succ (constantly 0) #(= % :G))]
    (is (= 5 cost))))
