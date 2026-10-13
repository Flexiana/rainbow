(ns rainbow.algorithms.proofs.ahof.forward-search
  "AHoF D33 Forward Search: finite-horizon lookahead planning. Building the search
  tree to the horizon, the value of a decision (max) node is the best value
  achievable among its action branches:

      lookahead a b = max(a, b)

  over the exact-rational action values (the two-action case; the k-action node
  folds this over the branches). Defined: the lookahead value as the max of the
  branch values. Proved native and axiom-free, as worked instances: lookahead 4 7
  = 7, and 4 <= lookahead 4 7 and 7 <= lookahead 4 7. That the lookahead value
  dominates every branch for all inputs, and the classical optimality of the
  extracted greedy action, are not proved here. The tree expansion, the successor
  generation, and the depth-horizon backups are executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.forward-search`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- lookahead [a b]
  (function/app (function/const* 'forward-search/lookahead []) a b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; lookahead a b = max(a, b)   (best of two action branches)
(def lookahead-spec
  {:name 'forward-search/lookahead :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]] (nnrat-max-term 'a 'b))})

(def definition-specs [lookahead-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; The decision node takes the better branch (values 4 and 7 -> 7).
(def lookahead-example-spec
  {:name 'forward-search/lookahead-example :universes []
   :type (equality nnrat (lookahead (whole 4) (whole 7)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (lookahead (whole 4) (whole 7)))})

;; Worked instance: 4 <= lookahead 4 7.
(def lookahead-above-a-spec
  {:name 'forward-search/lookahead-above-a :universes []
   :type (nnrat-at-most (whole 4) (lookahead (whole 4) (whole 7)))
   :value (at-most-proof (whole 4) (lookahead (whole 4) (whole 7)))})

;; Worked instance: 7 <= lookahead 4 7.
(def lookahead-above-b-spec
  {:name 'forward-search/lookahead-above-b :universes []
   :type (nnrat-at-most (whole 7) (lookahead (whole 4) (whole 7)))
   :value (at-most-proof (whole 7) (lookahead (whole 4) (whole 7)))})

(def theorem-specs
  [lookahead-example-spec lookahead-above-a-spec lookahead-above-b-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-forward-search (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.forward-search))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
