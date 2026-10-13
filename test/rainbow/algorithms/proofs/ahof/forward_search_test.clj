(ns rainbow.algorithms.proofs.ahof.forward-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.forward-search :as forward-search]
            [rainbow.algorithms.reference.forward-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          forward-search/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest forward-search-lookahead-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (forward-search/definition-ids checked-environment)
        theorems (forward-search/theorem-ids checked-environment)]
    (is (= #{'forward-search/lookahead} (set (keys definitions))))
    (is (= #{'forward-search/lookahead-example
             'forward-search/lookahead-above-a
             'forward-search/lookahead-above-b}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-forward-search-backs-up-values
  (is (= 7 (executable/lookahead 4 7)))
  ;; Two-step lookahead: from S, action a->A (reward 1) then A->G (reward 5) = 6;
  ;; action b->B (reward 4) then B->G (reward 1) = 5. Best is 6.
  (let [actions {:S [[:A 1] [:B 4]] :A [[:G 5]] :B [[:G 1]] :G []}]
    (is (= 6 (executable/value actions (constantly 0) 2 :S)))))
