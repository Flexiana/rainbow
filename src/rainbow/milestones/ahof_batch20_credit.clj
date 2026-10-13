(ns rainbow.milestones.ahof-batch20-credit
  "Twentieth batch: the signed-rational differentiation/quasi-Newton/gradient cluster --
  O1 O2 O3 O4 O5 O6 O7 O25 O27 O28 O29 O30 D50 D55 D80."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.math.rational.signed.multiply :as sm]
            [rainbow.algorithms.proofs.ahof.forward-difference :as o1]
            [rainbow.algorithms.proofs.ahof.central-difference :as o2]
            [rainbow.algorithms.proofs.ahof.complex-step :as o3]
            [rainbow.algorithms.proofs.ahof.forward-mode-ad :as o4]
            [rainbow.algorithms.proofs.ahof.reverse-mode-ad :as o5]
            [rainbow.algorithms.proofs.ahof.regression-gradient :as o6]
            [rainbow.algorithms.proofs.ahof.spsa :as o7]
            [rainbow.algorithms.proofs.ahof.hypergradient-hg :as o25]
            [rainbow.algorithms.proofs.ahof.secant :as o27]
            [rainbow.algorithms.proofs.ahof.dfp :as o28]
            [rainbow.algorithms.proofs.ahof.bfgs :as o29]
            [rainbow.algorithms.proofs.ahof.lbfgs :as o30]
            [rainbow.algorithms.proofs.ahof.natural-gradient-ng :as d50]
            [rainbow.algorithms.proofs.ahof.deterministic-pg :as d55]
            [rainbow.algorithms.proofs.ahof.game-ascent :as d80]))

(def AR [{:target/name 'nnrat/add :statement "exact-rational addition is present for the cross certificate"}
         {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present for the cross certificate"}])
(defn- m [e d t] [{:extend e :defs d :thms t}])
(defn- mm [e d t] [{:extend sm/extend-environment :defs sm/definition-ids :thms sm/theorem-ids}
                   {:extend e :defs d :thms t}])
(defn- cb [pairs] (into {:exact-rational-only true :signed-rational true} (map (fn [[k v]] [k v])) pairs))

(def configs
  [{:id "O1" :name "Forward Difference" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Forward finite difference (f(x+h)-f(x))/h; with h=1 the estimate is the signed difference."
    :kind :ahof-o1-forward-difference :dir "artifacts/ahof/o1-forward-difference"
    :modules (m o1/extend-environment o1/definition-ids o1/theorem-ids) :baseline-prereqs AR
    :package 'findiff/slope-is-three :claim-boundaries (cb {:signed-difference :proved :step-limit :not-claimed})
    :spec {:module 'findiff :headline 'findiff/forward-difference}}
   {:id "O2" :name "Central Difference" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Central finite difference (f(x+h)-f(x-h))/(2h); with 2h=1 the estimate is the signed difference."
    :kind :ahof-o2-central-difference :dir "artifacts/ahof/o2-central-difference"
    :modules (m o2/extend-environment o2/definition-ids o2/theorem-ids) :baseline-prereqs AR
    :package 'central-diff/slope-example-is-4 :claim-boundaries (cb {:signed-difference :proved})
    :spec {:module 'central-diff :headline 'central-diff/central-difference}}
   {:id "O3" :name "Complex-Step Derivative" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Complex-step derivative avoids subtractive cancellation; the estimate value is a signed directional slope."
    :kind :ahof-o3-complex-step :dir "artifacts/ahof/o3-complex-step"
    :modules (m o3/extend-environment o3/definition-ids o3/theorem-ids) :baseline-prereqs AR
    :package 'complex-step/slope-example-is-3 :claim-boundaries (cb {:signed-slope :proved :complex-arithmetic :not-claimed})
    :spec {:module 'complex-step :headline 'complex-step/derivative-estimate}}
   {:id "O4" :name "Forward-Mode Auto-Diff" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Dual-number forward-mode AD composes derivatives multiplicatively via the chain rule."
    :kind :ahof-o4-forward-mode-ad :dir "artifacts/ahof/o4-forward-mode-ad"
    :modules (mm o4/extend-environment o4/definition-ids o4/theorem-ids) :baseline-prereqs AR
    :package 'fwd-ad/chain-example-is-6 :claim-boundaries (cb {:chain-rule-product :proved :computation-graph :not-claimed})
    :spec {:module 'fwd-ad :headline 'fwd-ad/dual-derivative :reuses 'rainbow.math.rational.signed.multiply}}
   {:id "O5" :name "Reverse-Mode Auto-Diff" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Reverse-mode AD backpropagates adjoints, accumulating each node's adjoint as a sum of contributions."
    :kind :ahof-o5-reverse-mode-ad :dir "artifacts/ahof/o5-reverse-mode-ad"
    :modules (m o5/extend-environment o5/definition-ids o5/theorem-ids) :baseline-prereqs AR
    :package 'rev-ad/accumulate-example-is-3 :claim-boundaries (cb {:adjoint-accumulation :proved :tape :not-claimed})
    :spec {:module 'rev-ad :headline 'rev-ad/adjoint-accumulate}}
   {:id "O6" :name "Regression Gradient" :source-file "catalog/01_optimization_algorithms.md"
    :listing "The least-squares gradient is driven by the residual actual - predicted."
    :kind :ahof-o6-regression-gradient :dir "artifacts/ahof/o6-regression-gradient"
    :modules (m o6/extend-environment o6/definition-ids o6/theorem-ids) :baseline-prereqs AR
    :package 'reg-grad/residual-example-is-3 :claim-boundaries (cb {:residual :proved :design-matrix :not-claimed})
    :spec {:module 'reg-grad :headline 'reg-grad/residual}}
   {:id "O7" :name "SPSA" :source-file "catalog/01_optimization_algorithms.md"
    :listing "SPSA estimates the gradient from a two-sided perturbation difference."
    :kind :ahof-o7-spsa :dir "artifacts/ahof/o7-spsa"
    :modules (m o7/extend-environment o7/definition-ids o7/theorem-ids) :baseline-prereqs AR
    :package 'spsa/difference-example-is-2 :claim-boundaries (cb {:perturbation-difference :proved :random-directions :not-claimed})
    :spec {:module 'spsa :headline 'spsa/perturbation-difference}}
   {:id "O25" :name "Hypergradient Descent" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Adapt the learning rate online by a hypergradient correction: rate + adjustment."
    :kind :ahof-o25-hypergradient :dir "artifacts/ahof/o25-hypergradient"
    :modules (m o25/extend-environment o25/definition-ids o25/theorem-ids) :baseline-prereqs AR
    :package 'hypergrad-ng/update-example-is-3 :claim-boundaries (cb {:rate-update :proved :hypergradient-formula :not-claimed})
    :spec {:module 'hypergrad-ng :headline 'hypergrad-ng/rate-update}}
   {:id "O27" :name "Secant Method" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Secant root-finding uses the divided-difference value change f-new - f-old."
    :kind :ahof-o27-secant :dir "artifacts/ahof/o27-secant"
    :modules (m o27/extend-environment o27/definition-ids o27/theorem-ids) :baseline-prereqs AR
    :package 'secant/change-example-is-3 :claim-boundaries (cb {:value-change :proved :iteration :not-claimed})
    :spec {:module 'secant :headline 'secant/value-change}}
   {:id "O28" :name "DFP" :source-file "catalog/01_optimization_algorithms.md"
    :listing "DFP quasi-Newton update uses the step vector s = x_{k+1} - x_k."
    :kind :ahof-o28-dfp :dir "artifacts/ahof/o28-dfp"
    :modules (m o28/extend-environment o28/definition-ids o28/theorem-ids) :baseline-prereqs AR
    :package 'dfp/step-example-is-2 :claim-boundaries (cb {:step-vector :proved :rank-two-update :not-claimed})
    :spec {:module 'dfp :headline 'dfp/step-vector}}
   {:id "O29" :name "BFGS" :source-file "catalog/01_optimization_algorithms.md"
    :listing "BFGS quasi-Newton update uses the gradient change y = g_{k+1} - g_k."
    :kind :ahof-o29-bfgs :dir "artifacts/ahof/o29-bfgs"
    :modules (m o29/extend-environment o29/definition-ids o29/theorem-ids) :baseline-prereqs AR
    :package 'bfgs/change-example-is-3 :claim-boundaries (cb {:gradient-change :proved :hessian-update :not-claimed})
    :spec {:module 'bfgs :headline 'bfgs/gradient-change}}
   {:id "O30" :name "L-BFGS" :source-file "catalog/01_optimization_algorithms.md"
    :listing "L-BFGS stores recent (s, y) pairs; the gradient change is y = g_{k+1} - g_k."
    :kind :ahof-o30-lbfgs :dir "artifacts/ahof/o30-lbfgs"
    :modules (m o30/extend-environment o30/definition-ids o30/theorem-ids) :baseline-prereqs AR
    :package 'lbfgs/change-example-is-2 :claim-boundaries (cb {:gradient-change :proved :two-loop-recursion :not-claimed})
    :spec {:module 'lbfgs :headline 'lbfgs/gradient-change}}
   {:id "D50" :name "Natural Gradient" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Natural gradient preconditions by the inverse Fisher metric and steps: theta - step."
    :kind :ahof-d50-natural-gradient :dir "artifacts/ahof/d50-natural-gradient"
    :modules (m d50/extend-environment d50/definition-ids d50/theorem-ids) :baseline-prereqs AR
    :package 'nat-grad/update-example-is-3 :claim-boundaries (cb {:preconditioned-update :proved :fisher-inverse :not-claimed})
    :spec {:module 'nat-grad :headline 'nat-grad/update}}
   {:id "D55" :name "Deterministic Policy Gradient" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "The DPG gradient is the chain product of the action-value gradient and the policy Jacobian."
    :kind :ahof-d55-deterministic-pg :dir "artifacts/ahof/d55-deterministic-pg"
    :modules (mm d55/extend-environment d55/definition-ids d55/theorem-ids) :baseline-prereqs AR
    :package 'det-pg/gradient-example-is-6 :claim-boundaries (cb {:chain-product :proved :critic-baseline :not-claimed})
    :spec {:module 'det-pg :headline 'det-pg/policy-gradient :reuses 'rainbow.math.rational.signed.multiply}}
   {:id "D80" :name "Gradient Ascent (Games)" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Each player ascends its own payoff gradient: theta + step."
    :kind :ahof-d80-game-ascent :dir "artifacts/ahof/d80-game-ascent"
    :modules (m d80/extend-environment d80/definition-ids d80/theorem-ids) :baseline-prereqs AR
    :package 'game-ascent/ascent-example-is-3 :claim-boundaries (cb {:ascent-step :proved :equilibrium-convergence :not-claimed})
    :spec {:module 'game-ascent :headline 'game-ascent/ascent-step}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
