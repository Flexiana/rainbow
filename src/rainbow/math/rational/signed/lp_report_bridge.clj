(ns rainbow.math.rational.signed.lp-report-bridge
  "Proof producer that binds supplied numeric reports to original LP sums.

  All returned specs must check: the numeric inequality alone is insufficient.
  This is actual-plan bound evidence, not a universal feasible-candidate proof,
  proof of original-plan feasibility, or verification of lp/bound's executable.
  No runtime API is changed. Exact integers/ratios only; no rounded reports."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-pointwise-bridge :as pw]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- exact? [x] (or (integer? x) (ratio? x)))
(defn- equivalence [left right]
  {:type (app 'signed/equivalent left right)
   :value (#'lp/computed-equivalence left right)})

(defn report-specs
  "Return four REQUIRED proof specs for an explicit caller-supplied report.

  Achieved and bound equal the original standard-form primal and dual sums;
  dual = primal + reported gap. The fourth proof transports the actual-plan
  bound through those equalities. For minimization, standard-form literals are
  -achieved and -bound: the checked order is -achieved <= -bound. The :direction
  field is validated by a host guard, not represented as a kernel proposition.

  The host neither recomputes nor substitutes the supplied numeric fields.
  Malformed numeric fields throw; false mathematical claims produce proof terms
  for the independent kernel to reject. Check ALL specs, including equalities."
  [instance {:keys [achieved bound gap direction] :as report}]
  (when-not (and (contains? #{nil :maximize :minimize} (:sense instance))
                 (every? exact? [achieved bound gap])
                 (= direction (if (= :minimize (:sense instance)) :lower :upper)))
    (throw (ex-info "Expected exact LP report values and a matching direction"
                    {:error/category :lp-report/invalid-report :report report})))
  (let [minimize? (= :minimize (:sense instance))
        original (#'lp/standard-form instance)
        {:keys [x objective dual-objective]} (#'lp/instance-terms original)
        primal (objective x)
        dual dual-objective
        a (#'lp/signed-literal (if minimize? (- achieved) achieved))
        b (#'lp/signed-literal (if minimize? (- bound) bound))
        g (#'lp/signed-literal gap)
        a-eq (equivalence primal a)
        b-eq (equivalence dual b)
        gap-eq (equivalence dual (app 'signed/add primal g))
        bridge (pw/pointwise-bridge-spec instance)]
    {:orientation (if minimize? :negated-minimization :maximization)
     :specs (array-map
             :achieved a-eq
             :bound b-eq
             :gap gap-eq
             :numeric-order
             {:type (app 'signed/at-most a b)
              :value (app 'signed/at-most-respects-equivalence
                          primal a dual b (:value a-eq) (:value b-eq)
                          (:value bridge))})}))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-pointwise-bridge])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  checked-environment)

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-report-bridge))
