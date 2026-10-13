(ns rainbow.milestones.ahof-batch16-credit
  "Sixteenth batch: ten fresh native proofs -- V35 Zonotope, V36 Ellipsoid,
  V37 Support Function, V38 Order Reduction, V39 LP Reachability, V43 Taylor
  Model, V45 Optimization-Based Reach, V49 Symbolic Reachability,
  O71 Grammatical Evolution, D60 Bayes-Adaptive MDP."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.zonotope :as zono]
            [rainbow.algorithms.proofs.ahof.ellipsoid :as elli]
            [rainbow.algorithms.proofs.ahof.support-function :as supf]
            [rainbow.algorithms.proofs.ahof.order-reduction :as ordr]
            [rainbow.algorithms.proofs.ahof.lp-reachability :as lpr]
            [rainbow.algorithms.proofs.ahof.taylor-model :as tay]
            [rainbow.algorithms.proofs.ahof.opt-reachability :as optr]
            [rainbow.algorithms.proofs.ahof.symbolic-reachability :as sym]
            [rainbow.algorithms.proofs.ahof.grammatical-evolution :as ge]
            [rainbow.algorithms.proofs.ahof.bayes-adaptive-mdp :as bam]))

(def AT [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the certificate"}])
(def IF [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'logic/if-data :statement "eliminator is present for the max"}])
(def AR [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
         {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}])

(defn- m [mod] [{:extend (:e mod) :defs (:d mod) :thms (:t mod)}])

(def configs
  [{:id "V35" :name "Zonotope Propagation" :source-file "catalog/03_validation_algorithms.md"
    :listing "Represent a reachable set as a zonotope; a point is inside when each generator coordinate stays within its unit bound."
    :kind :ahof-v35-zonotope :dir "artifacts/ahof/v35-zonotope"
    :modules (m {:e zono/extend-environment :d zono/definition-ids :t zono/theorem-ids})
    :baseline-prereqs AT :package 'zonotope/within-generator-inside
    :claim-boundaries {:exact-rational-only true :generator-bound-membership :proved :order-growth :not-claimed}
    :spec {:module 'zonotope :headline 'zonotope/in-zonotope?}}
   {:id "V36" :name "Ellipsoid Propagation" :source-file "catalog/03_validation_algorithms.md"
    :listing "Over-approximate a reachable set by an ellipsoid; a point is inside when its quadratic form is within the limit."
    :kind :ahof-v36-ellipsoid :dir "artifacts/ahof/v36-ellipsoid"
    :modules (m {:e elli/extend-environment :d elli/definition-ids :t elli/theorem-ids})
    :baseline-prereqs AT :package 'ellipsoid/within-ellipsoid-inside
    :claim-boundaries {:exact-rational-only true :quadratic-form-membership :proved :shape-matrix-update :not-claimed}
    :spec {:module 'ellipsoid :headline 'ellipsoid/in-ellipsoid?}}
   {:id "V37" :name "Support Function Method" :source-file "catalog/03_validation_algorithms.md"
    :listing "Represent a convex set by its support function; a halfspace is respected when the support value in that direction is within the bound."
    :kind :ahof-v37-support-function :dir "artifacts/ahof/v37-support-function"
    :modules (m {:e supf/extend-environment :d supf/definition-ids :t supf/theorem-ids})
    :baseline-prereqs AT :package 'support-fn/support-within-bound
    :claim-boundaries {:exact-rational-only true :support-bound-decision :proved :directional-sampling :not-claimed}
    :spec {:module 'support-fn :headline 'support-fn/within-support?}}
   {:id "V38" :name "Order Reduction" :source-file "catalog/03_validation_algorithms.md"
    :listing "Reduce the representation order while over-approximating; sound when the incurred error stays within tolerance."
    :kind :ahof-v38-order-reduction :dir "artifacts/ahof/v38-order-reduction"
    :modules (m {:e ordr/extend-environment :d ordr/definition-ids :t ordr/theorem-ids})
    :baseline-prereqs AT :package 'order-reduction/small-error-sound
    :claim-boundaries {:exact-rational-only true :error-tolerance-decision :proved :reduction-heuristic :not-claimed}
    :spec {:module 'order-reduction :headline 'order-reduction/reduction-sound?}}
   {:id "V39" :name "LP-Based Reachability" :source-file "catalog/03_validation_algorithms.md"
    :listing "Compute reachable-set bounds via linear programs; reachable within a facet when the LP objective stays within the facet bound."
    :kind :ahof-v39-lp-reachability :dir "artifacts/ahof/v39-lp-reachability"
    :modules (m {:e lpr/extend-environment :d lpr/definition-ids :t lpr/theorem-ids})
    :baseline-prereqs AT :package 'lp-reach/objective-within-facet
    :claim-boundaries {:exact-rational-only true :facet-bound-decision :proved :lp-solver :not-claimed}
    :spec {:module 'lp-reach :headline 'lp-reach/lp-reachable?}}
   {:id "V43" :name "Taylor Model Propagation" :source-file "catalog/03_validation_algorithms.md"
    :listing "Represent a function by a polynomial plus a guaranteed remainder interval; valid when the remainder magnitude stays within the bound."
    :kind :ahof-v43-taylor-model :dir "artifacts/ahof/v43-taylor-model"
    :modules (m {:e tay/extend-environment :d tay/definition-ids :t tay/theorem-ids})
    :baseline-prereqs AT :package 'taylor/small-remainder-valid
    :claim-boundaries {:exact-rational-only true :remainder-bound-decision :proved :polynomial-arithmetic :not-claimed}
    :spec {:module 'taylor :headline 'taylor/remainder-bounded?}}
   {:id "V45" :name "Optimization-Based Reach" :source-file "catalog/03_validation_algorithms.md"
    :listing "Bound the reachable set by solving an optimization per direction; certified when the optimal reach value stays within the bound."
    :kind :ahof-v45-opt-reachability :dir "artifacts/ahof/v45-opt-reachability"
    :modules (m {:e optr/extend-environment :d optr/definition-ids :t optr/theorem-ids})
    :baseline-prereqs AT :package 'opt-reach/reach-within-bound
    :claim-boundaries {:exact-rational-only true :reach-bound-decision :proved :nonconvex-optimizer :not-claimed}
    :spec {:module 'opt-reach :headline 'opt-reach/reach-bounded?}}
   {:id "V49" :name "Symbolic Reachability (BDDs)" :source-file "catalog/03_validation_algorithms.md"
    :listing "Represent reachable state sets symbolically (BDDs) and test membership; a state is in the set when within the radius of a representative."
    :kind :ahof-v49-symbolic-reachability :dir "artifacts/ahof/v49-symbolic-reachability"
    :modules (m {:e sym/extend-environment :d sym/definition-ids :t sym/theorem-ids})
    :baseline-prereqs AT :package 'symbolic/within-set-member
    :claim-boundaries {:exact-rational-only true :set-membership-decision :proved :bdd-encoding :not-claimed}
    :spec {:module 'symbolic :headline 'symbolic/in-symbolic-set?}}
   {:id "O71" :name "Grammatical Evolution" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Evolve programs by mapping integer genomes through a BNF grammar, selecting by fitness; keep the fitter individual."
    :kind :ahof-o71-grammatical-evolution :dir "artifacts/ahof/o71-grammatical-evolution"
    :modules (m {:e ge/extend-environment :d ge/definition-ids :t ge/theorem-ids})
    :baseline-prereqs IF :package 'grammar-evo/best-fitness-is-maximum
    :claim-boundaries {:exact-rational-only true :fitness-max-selection :proved :genotype-phenotype-map :not-claimed}
    :spec {:module 'grammar-evo :headline 'grammar-evo/best-fitness}}
   {:id "D60" :name "Bayes-Adaptive MDP" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Plan in the belief-MDP over unknown parameters; an action's value is the posterior-belief-weighted average of its value under each candidate model."
    :kind :ahof-d60-bayes-adaptive-mdp :dir "artifacts/ahof/d60-bayes-adaptive-mdp"
    :modules (m {:e bam/extend-environment :d bam/definition-ids :t bam/theorem-ids})
    :baseline-prereqs AR :package 'bamdp/bayes-adaptive
    :claim-boundaries {:exact-rational-only true :belief-weighted-value :proved :posterior-update :not-claimed}
    :spec {:module 'bamdp :headline 'bamdp/expected-value}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
