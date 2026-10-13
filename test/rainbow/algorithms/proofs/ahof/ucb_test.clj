(ns rainbow.algorithms.proofs.ahof.ucb-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.ucb :as ucb]
            [rainbow.algorithms.reference.ucb :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ucb/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest ucb-acquisition-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ucb/definition-ids checked-environment)
        theorems (ucb/theorem-ids checked-environment)]
    (is (= #{'ucb/acquisition} (set (keys definitions))))
    (is (= #{'ucb/acquisition-unfold
             'ucb/acquisition-example
             'ucb/at-least-mean
             'ucb/at-least-mean-universal}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-ucb-selects-optimistically
  (is (= 7 (executable/acquisition 5 1 2)))
  ;; Candidate b has a lower mean but higher uncertainty; with weight 2 its UCB
  ;; (4 + 2*3 = 10) beats a's (6 + 2*1 = 8), so exploration wins.
  (let [predict {:a [6 1] :b [4 3]}]
    (is (= :b (executable/select predict 2 [:a :b])))))
