(ns rainbow.algorithms.proofs.ahof.natural-inclusion
  "AHoF V41 Natural Inclusion Function: replace each variable in an expression by its
  interval and evaluate with interval arithmetic to get a guaranteed enclosure [lo, hi]
  of the range; the true range is contained, so a candidate value is certified within
  the enclosure exactly when it lies between the bounds:

      encloses? lo hi value = (lo <= value) AND (value <= hi)

  (boolean AND via logic/if-data over the two exact-rational order decisions). Proved
  native and axiom-free: the enclosure test with its unfold, an enclosed value, and a
  value below the lower bound. Requires audit/decide-nnrat-at-most, logic/if-data
  (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.natural-inclusion`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))
(defn- encloses? [lo hi value]
  (function/app (function/const* 'nat-incl/encloses? []) lo hi value))

(def encloses-spec
  {:name 'nat-incl/encloses? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam [['lo nnrat] ['hi nnrat] ['value nnrat]]
                        (and-bool (decide-at-most 'lo 'value) (decide-at-most 'value 'hi)))})

(def definition-specs [encloses-spec])

(def encloses-unfold-spec
  {:name 'nat-incl/encloses-unfold :universes []
   :type (function/forall [['lo nnrat] ['hi nnrat] ['value nnrat]]
                          (equality bool (encloses? 'lo 'hi 'value)
                                    (and-bool (decide-at-most 'lo 'value)
                                              (decide-at-most 'value 'hi))))
   :value (function/lam [['lo nnrat] ['hi nnrat] ['value nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      bool (encloses? 'lo 'hi 'value)))})

;; The range value 1 is enclosed by [1/2, 3/2].
(def value-enclosed-spec
  {:name 'nat-incl/value-enclosed :universes []
   :type (equality bool (encloses? (fraction 1 1) (fraction 3 1) (whole 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (encloses? (fraction 1 1) (fraction 3 1) (whole 1)))})

;; A value 1/4 below the lower bound 1/2 is not enclosed.
(def value-below-not-enclosed-spec
  {:name 'nat-incl/value-below-not-enclosed :universes []
   :type (equality bool (encloses? (fraction 1 1) (fraction 3 1) (fraction 1 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (encloses? (fraction 1 1) (fraction 3 1) (fraction 1 3)))})

(def theorem-specs
  [encloses-unfold-spec value-enclosed-spec value-below-not-enclosed-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-natural-inclusion (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.natural-inclusion))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
