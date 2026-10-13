(ns rainbow.milestones.ahof-batch7-credit
  "Seventh batch: three fresh native proofs -- O74 Robust Optimization,
  D66 Discrete State Filter, O10 Quadratic Fit Search."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.robust-optimization :as ro]
            [rainbow.algorithms.proofs.ahof.discrete-filter :as df]
            [rainbow.algorithms.proofs.ahof.quadratic-fit :as qf]))

(def configs
  [{:id "O74" :name "Robust Optimization (set-based)"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Optimize against the worst case over an uncertainty set: the worst-case cost is the maximum over scenarios; a design is acceptable when it stays within budget."
    :kind :ahof-o74-robust-optimization
    :dir "artifacts/ahof/o74-robust-optimization"
    :modules [{:extend ro/extend-environment :defs ro/definition-ids :thms ro/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the max"}]
    :package 'robust-opt/worst-case-is-larger
    :claim-boundaries {:exact-rational-only true :worst-case-maximum :proved :robust-acceptance-threshold :proved
                       :continuous-uncertainty-set :not-claimed :minimax-optimization :not-claimed}
    :spec {:module 'robust-opt :headline 'robust-opt/worst-case}}
   {:id "D66" :name "Discrete State Filter"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Recursive Bayesian filtering over a finite state space: unnormalized posterior weight = measurement likelihood * prior belief, then renormalize."
    :kind :ahof-d66-discrete-filter
    :dir "artifacts/ahof/d66-discrete-filter"
    :modules [{:extend df/extend-environment :defs df/definition-ids :thms df/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}
                       {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present for the weight values"}]
    :package 'discrete-filter/discrete-filter
    :claim-boundaries {:exact-rational-only true :bayes-posterior-weight :proved :belief-concentration :proved
                       :normalization-constant :not-claimed :transition-model :not-claimed}
    :spec {:module 'discrete-filter :headline 'discrete-filter/posterior-weight}}
   {:id "O10" :name "Quadratic Fit Search"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Fit a parabola through three points and step toward its vertex, retaining the three lowest-valued samples; the bracket-tracking core is the minimum of the three values."
    :kind :ahof-o10-quadratic-fit
    :dir "artifacts/ahof/o10-quadratic-fit"
    :modules [{:extend qf/extend-environment :defs qf/definition-ids :thms qf/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the min"}]
    :package 'quadfit/keeps-smallest
    :claim-boundaries {:exact-rational-only true :three-way-minimum :proved :bracket-retains-best :proved
                       :parabola-vertex-formula :not-claimed :convergence-rate :not-claimed}
    :spec {:module 'quadfit :headline 'quadfit/best-of-three}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
