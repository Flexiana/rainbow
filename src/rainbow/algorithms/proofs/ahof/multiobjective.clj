(ns rainbow.algorithms.proofs.ahof.multiobjective
  "Kochenderfer 'Algorithms for Optimization' Ch.15-16 multiobjective / sampling-plan
  selection rules as higher-order-function compositions, proved axiom-free, extending
  the 222 AHoF catalog:

    O15.3 non-dominated sorting : a Pareto-dominates b  iff  a1>=b1 AND a2>=b2
    O15.4 VEGA                  : per-objective subpopulation selection = max fitness
    O16.8 greedy subset select  : pick the point of minimum distance metric
    O16.9 exchange subset select: accept a swap only when it reduces the metric

  Pareto dominance is a boolean-AND of two decidable >= tests; its soundness
  (dominates=true entails both objective inequalities) reuses rainbow.math.logic.boolean-and
  exactly as interval-membership-soundness does.  Selection reuses nnrat-minmax.
  Native and axiom-free; chains boolean-and and nnrat-minmax on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.boolean-and :as ba]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- eq-nnrat [l r] (function/equality type-level nnrat l r))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- decide-at-most [a b]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) a b))
(defn- and-op [a b] (function/app (function/const* 'boolean/and []) a b))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- if-data [decision then else]
  (function/app (function/const* 'logic/if-data [type-level]) nnrat (eq-bool decision decision)
                decision then else))
(defn- reflexive-nnrat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nnrat v))

;; ---- O15.3 Pareto dominance (a >= b in both maximization objectives) ---------
(def dominates-spec
  {:name 'mo/dominates :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat bool)
   :value (function/lam [['a1 nnrat] ['a2 nnrat] ['b1 nnrat] ['b2 nnrat]]
                        (and-op (decide-at-most 'b1 'a1) (decide-at-most 'b2 'a2)))})

;; dominates = true  ->  (b1 <= a1) AND (b2 <= a2)
(def dominates-sound-spec
  {:name 'mo/dominates-sound :universes []
   :type (function/forall
          [['a1 nnrat] ['a2 nnrat] ['b1 nnrat] ['b2 nnrat]
           ['h (eq-bool (function/app (function/const* 'mo/dominates []) 'a1 'a2 'b1 'b2)
                        true-value)]]
          (conjunction (at-most 'b1 'a1) (at-most 'b2 'a2)))
   :value (function/lam
           [['a1 nnrat] ['a2 nnrat] ['b1 nnrat] ['b2 nnrat]
            ['h (eq-bool (function/app (function/const* 'mo/dominates []) 'a1 'a2 'b1 'b2)
                         true-value)]]
           (let [dl (decide-at-most 'b1 'a1)
                 dr (decide-at-most 'b2 'a2)
                 left-true (function/app (function/const* 'boolean/and-implies-left []) dl dr 'h)
                 right-true (function/app (function/const* 'boolean/and-implies-right []) dl dr 'h)]
             (function/app
              (function/const* 'proposition/conjoin [])
              (at-most 'b1 'a1) (at-most 'b2 'a2)
              (function/app (function/const* 'nnrat/decide-at-most-true-sound []) 'b1 'a1 left-true)
              (function/app (function/const* 'nnrat/decide-at-most-true-sound []) 'b2 'a2 right-true))))})

;; ---- O15.4 VEGA: per-objective selection keeps the higher fitness ------------
(def vega-select-spec
  {:name 'mo/vega-select :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['fa nnrat] ['fb nnrat]] (rmax 'fa 'fb))})

(def vega-keeps-fittest-left-spec
  {:name 'mo/vega-keeps-fittest-left :universes []
   :type (function/forall [['fa nnrat] ['fb nnrat]]
                          (at-most 'fa (function/app (function/const* 'mo/vega-select []) 'fa 'fb)))
   :value (function/lam [['fa nnrat] ['fb nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'fa 'fb))})

(def vega-keeps-fittest-right-spec
  {:name 'mo/vega-keeps-fittest-right :universes []
   :type (function/forall [['fa nnrat] ['fb nnrat]]
                          (at-most 'fb (function/app (function/const* 'mo/vega-select []) 'fa 'fb)))
   :value (function/lam [['fa nnrat] ['fb nnrat]]
                        (function/app (function/const* 'minmax/max-upper-right []) 'fa 'fb))})

;; ---- O16.8 greedy subset selection: keep the point of minimum distance -------
(def greedy-nearest-spec
  {:name 'mo/greedy-nearest :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['d0 nnrat] ['d1 nnrat]] (rmin 'd0 'd1))})

(def greedy-nearest-below-left-spec
  {:name 'mo/greedy-nearest-below-left :universes []
   :type (function/forall [['d0 nnrat] ['d1 nnrat]]
                          (at-most (function/app (function/const* 'mo/greedy-nearest []) 'd0 'd1) 'd0))
   :value (function/lam [['d0 nnrat] ['d1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-left []) 'd0 'd1))})

(def greedy-nearest-below-right-spec
  {:name 'mo/greedy-nearest-below-right :universes []
   :type (function/forall [['d0 nnrat] ['d1 nnrat]]
                          (at-most (function/app (function/const* 'mo/greedy-nearest []) 'd0 'd1) 'd1))
   :value (function/lam [['d0 nnrat] ['d1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-right []) 'd0 'd1))})

;; ---- O16.9 exchange subset selection: accept a swap only if it improved ------
(def exchange-step-spec
  {:name 'mo/exchange-step :kind :definition :universes []
   :type (function/arrow bool nnrat nnrat nnrat)
   :value (function/lam [['improved bool] ['candidate nnrat] ['current nnrat]]
                        (if-data 'improved 'candidate 'current))})

(def exchange-accepts-spec
  {:name 'mo/exchange-accepts :universes []
   :type (function/forall [['candidate nnrat] ['current nnrat]]
                          (eq-nnrat (function/app (function/const* 'mo/exchange-step [])
                                                  true-value 'candidate 'current)
                                    'candidate))
   :value (function/lam [['candidate nnrat] ['current nnrat]]
                        (reflexive-nnrat 'candidate))})

(def exchange-rejects-spec
  {:name 'mo/exchange-rejects :universes []
   :type (function/forall [['candidate nnrat] ['current nnrat]]
                          (eq-nnrat (function/app (function/const* 'mo/exchange-step [])
                                                  false-value 'candidate 'current)
                                    'current))
   :value (function/lam [['candidate nnrat] ['current nnrat]]
                        (reflexive-nnrat 'current))})

(def definition-specs
  [dominates-spec vega-select-spec greedy-nearest-spec exchange-step-spec])
(def theorem-specs
  [dominates-sound-spec vega-keeps-fittest-left-spec vega-keeps-fittest-right-spec
   greedy-nearest-below-left-spec greedy-nearest-below-right-spec
   exchange-accepts-spec exchange-rejects-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.logic.boolean-and rainbow.math.rational.nnrat.minmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-multiobjective (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.multiobjective))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
