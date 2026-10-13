(ns rainbow.milestones.ahof-batch5-credit
  "Fifth batch: O68 (existing pareto module) plus two fresh native proofs
  (O72 Branch and Bound via lemma reuse, D27 Linear Interpolation)."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.branch-and-bound :as bnb]
            [rainbow.algorithms.proofs.ahof.pareto :as pareto]
            [rainbow.algorithms.proofs.ahof.o72-branch-and-bound :as o72]
            [rainbow.algorithms.proofs.ahof.linear-interpolation :as lerp]))

(def configs
  [{:id "O68" :name "Pareto Filter"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Weak Pareto dominance for a two-objective minimization problem: a dominates b when a is no worse than b in every objective."
    :kind :ahof-o68-pareto
    :dir "artifacts/ahof/o68-pareto"
    :modules [{:extend pareto/extend-environment :defs pareto/definition-ids :thms pareto/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "boolean eliminator is present for conjunction"}]
    :package 'pareto/dominates-example
    :claim-boundaries {:exact-rational-only true :two-objective-weak-dominance :proved
                       :arbitrary-objective-count :not-claimed :full-front-construction :not-claimed}
    :spec {:module 'pareto :headline 'pareto/dominates?}}
   {:id "O72" :name "Branch and Bound"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Optimization Branch and Bound: prune a subtree when its optimistic bound cannot beat the incumbent (shares D34's bounding structure)."
    :kind :ahof-o72-branch-and-bound
    :dir "artifacts/ahof/o72-branch-and-bound"
    :modules [{:extend bnb/extend-environment :defs bnb/definition-ids :thms bnb/theorem-ids}
              {:extend o72/extend-environment :defs o72/definition-ids :thms o72/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for pruning soundness"}]
    :package 'ahof-o72/branch-and-bound
    :claim-boundaries {:exact-rational-only true :bound-domination-test :proved :pruning-soundness :proved
                       :branching-strategy :not-claimed :full-tree-optimality :not-claimed}
    :spec {:module 'ahof-o72 :headline 'ahof-o72/branch-and-bound :reuses 'rainbow.algorithms.proofs.branch-and-bound}}
   {:id "D27" :name "Linear Interpolation"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Linear interpolation / convex combination of two values: lerp a b w0 w1 = w0*a + w1*b."
    :kind :ahof-d27-linear-interpolation
    :dir "artifacts/ahof/d27-linear-interpolation"
    :modules [{:extend lerp/extend-environment :defs lerp/definition-ids :thms lerp/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'interp/linear-interpolation
    :claim-boundaries {:exact-rational-only true :convex-combination :proved :endpoints-and-midpoint :proved
                       :multivariate-interpolation :not-claimed}
    :spec {:module 'interp :headline 'interp/linear-interpolation}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
