(ns rainbow.algorithms.proofs.ahof.local-policy-search
  "AHoF D40 Local Policy Search: hill climbing in policy-parameter space. Each
  iteration perturbs the current policy, evaluates the neighbor, and keeps
  whichever policy scores higher (for a return/value to be maximized). The
  improvement step keeps the better of the incumbent and the neighbor value:

      improve incumbent neighbor = max(incumbent, neighbor)

  over the decidable rational order (improve is defined as that max). Proved
  native and axiom-free, as worked instances: improve(5, 7) = 7; and the worked
  certificates 5 <= improve(5, 7) and 7 <= improve(5, 7) (native nnrat/at-most).
  That the step never decreases the incumbent for all inputs, so that local
  search is an ascent, is the algorithm's classical property, not proved here.
  The perturbation and the policy evaluation are executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.local-policy-search`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
;; max a b = if (a <= b) then b else a
(defn- nnrat-max-term [a b] (if-value (decide-at-most a b) b a))

(defn- improve [incumbent neighbor]
  (function/app (function/const* 'local-policy-search/improve [])
                incumbent neighbor))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; improve incumbent neighbor = max(incumbent, neighbor)
(def improve-spec
  {:name 'local-policy-search/improve :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['incumbent nnrat] ['neighbor nnrat]]
                        (nnrat-max-term 'incumbent 'neighbor))})

(def definition-specs [improve-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A better neighbor (value 7) is adopted over the incumbent (value 5).
(def improve-adopts-better-spec
  {:name 'local-policy-search/improve-adopts-better :universes []
   :type (equality nnrat (improve (whole 5) (whole 7)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (improve (whole 5) (whole 7)))})

;; Worked certificate (incumbent): 5 <= improve(5, 7).
(def improve-above-incumbent-spec
  {:name 'local-policy-search/improve-above-incumbent :universes []
   :type (nnrat-at-most (whole 5) (improve (whole 5) (whole 7)))
   :value (at-most-proof (whole 5) (improve (whole 5) (whole 7)))})

;; Worked certificate (neighbor): 7 <= improve(5, 7).
(def improve-above-neighbor-spec
  {:name 'local-policy-search/improve-above-neighbor :universes []
   :type (nnrat-at-most (whole 7) (improve (whole 5) (whole 7)))
   :value (at-most-proof (whole 7) (improve (whole 5) (whole 7)))})

(def theorem-specs
  [improve-adopts-better-spec improve-above-incumbent-spec
   improve-above-neighbor-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-local-policy-search
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
