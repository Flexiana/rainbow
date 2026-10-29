(ns rainbow.math.rational.signed.lp-witness-bridge
  "Original standard-form primal/dual witnesses and a reported universal bound.
  Experimental proof producer, not a verifier or API success policy. Each spec
  must be checked against an independently reconstructed target. This uses the
  existing literal/standard-form interpretation; it does not prove host semantics."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-report-bridge :as report]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- all-le [left right indices]
  (f/app (f/const* 'signed/all-at-most [[:zero]]) lp/nat left right indices))
(defn- witness [left right indices n]
  {:type (all-le left right indices)
   :value (#'lp/all-at-most-proof left right n)})

(defn witness-specs
  "Emit four separate feasibility/nonnegativity witnesses and a universal bound.

  The universal target quantifies over EVERY Nat-indexed signed candidate that
  satisfies the original listed row constraints and column nonnegativity. Its
  endpoint is the supplied reported bound (negated for minimization). No premise
  assumes the submitted plan feasible: that fact is a separate required witness
  if a consumer wants both feasibility and a bound. The producer supports the
  exact dual-objective endpoint, not arbitrary looser reported bounds.

  Instance encoding is the existing standard-form interpretation. Callers must
  apply their validated input domain and kernel-check the emitted evidence."
  [instance reported-bound]
  (when-not (and (or (integer? reported-bound) (ratio? reported-bound))
                 (<= -10000 (if (ratio? reported-bound)
                              (numerator reported-bound) reported-bound) 10000)
                 (<= 1 (if (ratio? reported-bound) (denominator reported-bound) 1) 10000)
                 (contains? #{nil :maximize :minimize} (:sense instance)))
    (throw (ex-info "Expected bounded exact reported endpoint and a supported sense"
                    {:error/category :lp-witness/invalid-endpoint})))
  (let [standard (#'lp/standard-form instance)
        {:keys [M b c x y rows cols row-count column-count
                row-activity dual-price zero-on objective dual-objective]}
        (#'lp/instance-terms standard)
        primal (witness (row-activity x) b rows row-count)
        primal-nn (witness (zero-on) x cols column-count)
        dual (witness c dual-price cols column-count)
        dual-nn (witness (zero-on) y rows row-count)
        bound (#'lp/signed-literal (if (= :minimize (:sense instance))
                                    (- reported-bound) reported-bound))
        endpoint-eq (#'lp/computed-equivalence dual-objective bound)
        candidate-obj (objective 'candidate)
        bindings [['candidate (f/arrow lp/nat lp/signed)]
                  ['feasible (all-le (row-activity 'candidate) b rows)]
                  ['nonnegative (all-le (zero-on) 'candidate cols)]]
        candidate-bound
        (f/app (f/const* 'optimization/signed-lp-weak-duality-on [[:zero]])
               lp/nat lp/nat M b c 'candidate y rows cols
               'feasible (:value dual) 'nonnegative (:value dual-nn))]
    (array-map
     :primal-feasibility primal
     :primal-nonnegative primal-nn
     :dual-feasibility dual
     :dual-nonnegative dual-nn
     :universal-reported-bound
     {:type (f/forall bindings (app 'signed/at-most candidate-obj bound))
      :value (f/lam bindings
                    (app 'signed/at-most-respects-equivalence
                         candidate-obj candidate-obj dual-objective bound
                         (app 'signed/equivalent-reflexive candidate-obj)
                         endpoint-eq candidate-bound))})))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-report-bridge])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  checked-environment)

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-witness-bridge))
