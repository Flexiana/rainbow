(ns rainbow.algorithms.proofs.branch-and-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.branch-and-bound :as bnb]
            [rainbow.algorithms.reference.branch-and-bound :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bnb/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest branch-and-bound-pruning-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bnb/definition-ids checked-environment)
        theorems (bnb/theorem-ids checked-environment)]
    (is (= #{'branch-and-bound/dominated?} (set (keys definitions))))
    (is (= #{'branch-and-bound/prunes-dominated-node
             'branch-and-bound/pruned-bound-dominated
             'branch-and-bound/explores-promising-node}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-branch-and-bound-prunes-soundly
  ;; Domination matches the proved predicate.
  (is (true? (executable/dominated? 3 5)))
  (is (false? (executable/dominated? 7 5)))
  ;; Frontier pruning drops only the dominated nodes.
  (is (= [{:b 7} {:b 6}]
         (executable/prune-frontier 5 [{:b 3} {:b 7} {:b 6}] :b)))
  ;; End-to-end: pruning never discards the optimum. A tiny maximization tree
  ;; where one subtree's bound cannot beat a known leaf still returns the true
  ;; best. Tree: root -> {A (leaf 8), B (bound 5, leaf 4)}; incumbent 8 prunes B.
  (let [children {:root [:a :b] :a [] :b []}
        bound {:root 100 :a 8 :b 5}
        value {:a 8 :b 4}]
    (is (= 8 (executable/best-leaf-value children bound value :root)))))
