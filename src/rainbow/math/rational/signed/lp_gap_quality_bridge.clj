(ns rainbow.math.rational.signed.lp-gap-quality-bridge
  "LP instantiation of additive epsilon quality for ORIGINAL constraints/plans.
  Untrusted producer. Thirteen specs are NOT the optimality verifier's thirteen:
  these add gap-within-budget and epsilon-optimal, not exact optimality."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.gap-quality :as quality]
            [rainbow.math.rational.signed.lp-plan-report-bridge :as plan]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
      (f/lam [['ignored lp/nat]] (f/const* 'signed/zero []))))
(defn epsilon-specs
  "Eleven original plan/report obligations plus gap<=epsilon and original-model
  epsilon-optimality (feasible plan AND all candidate improvements <=epsilon).
  Epsilon is an exact signed rational; impossible budgets generate rejectable
  proof values, never an accepted claim or a decision of suboptimality."
  [original actual report epsilon]
  (when-not (and (or (integer? epsilon) (ratio? epsilon))
                 (<= -10000 (if (ratio? epsilon) (numerator epsilon) epsilon) 10000)
                 (<= 1 (if (ratio? epsilon) (denominator epsilon) 1) 10000))
    (throw (ex-info "Expected bounded exact epsilon before encoding"
                    {:error/category :lp-gap-quality/domain})))
  (let [specs (plan/plan-report-specs original actual report)
        universal (:universal-original-bound specs)
        ;; Producer-internal composition only, NOT receiver-side target selection.
        bindings (second (:type universal))
        candidate-binding (first bindings) feasible-body (second (second bindings))
        P (f/lam [candidate-binding] feasible-body)
        c (mapping (:margins original)) x (mapping (:plan original))
        cols (#'lp/index-list (count (:margins original)))
        F (f/lam [candidate-binding]
                 (f/app (f/const* 'signed/map-sum [[:zero]]) lp/nat
                        (f/lam [['i lp/nat]]
                               (app 'signed/multiply (f/app c 'i) (f/app 'candidate 'i))) cols))
        [A B G E] (mapv #'lp/signed-literal [(:achieved report) (:bound report) (:gap report) epsilon])
        budget {:type (app 'signed/at-most G E) :value (#'lp/decided-at-most G E)}
        minimum? (= :minimize (:sense original))
        X (f/app F x) Y (f/app F 'candidate)
        difference (if minimum? (app 'signed/subtract X Y) (app 'signed/subtract Y X))
        target (app 'proposition/conjunction (f/app P x)
                    (f/forall [candidate-binding ['original-feasible (f/app P 'candidate)]]
                              (app 'signed/at-most difference E)))
        proof (f/app (f/const* (if minimum? 'optimization/signed-lower-gap-epsilon-optimal
                                  'optimization/signed-upper-gap-epsilon-optimal) [[:zero]])
                     (f/arrow lp/nat lp/signed) F P x A B G E
                     (:value (:submitted-plan-feasible specs)) (:value (:achieved-value specs))
                     (:value (:reported-gap specs)) (:value universal) (:value budget))]
    (assoc specs :gap-within-budget budget :epsilon-optimal {:type target :value proof})))
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-plan-report-bridge rainbow.math.rational.signed.gap-quality])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-gap-quality-bridge))
