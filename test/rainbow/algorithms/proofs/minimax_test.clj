(ns rainbow.algorithms.proofs.minimax-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.minimax :as minimax]
            [rainbow.algorithms.reference.minimax :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          minimax/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest minimax-value-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (minimax/definition-ids checked-environment)
        theorems (minimax/theorem-ids checked-environment)]
    (is (= #{'minimax/value} (set (keys definitions))))
    (is (= #{'minimax/value-example
             'minimax/value-secures-best-move
             'minimax/value-dominates-other-move}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-minimax-matches-the-value
  (is (= 2 (executable/value 3 1 2 4)))
  ;; The explicit-tree minimax agrees with the two-ply combinator.
  (let [tree {:maximizing? true
              :children [{:maximizing? false
                          :children [{:leaf 3} {:leaf 1}]}
                         {:maximizing? false
                          :children [{:leaf 2} {:leaf 4}]}]}]
    (is (= 2 (executable/minimax tree))))
  ;; A leaf is its own value.
  (is (= 7 (executable/minimax {:leaf 7}))))
