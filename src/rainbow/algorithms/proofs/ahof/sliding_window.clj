(ns rainbow.algorithms.proofs.ahof.sliding-window
  "AHoF Sliding Window: solve subarray/substring problems in one O(n) pass by
  maintaining a window that slides across the data, adding the entering element and
  removing the leaving one instead of recomputing over each subarray. For a
  variable-size window under a budget (e.g. longest subarray whose sum stays within
  a limit), the window is VALID while its running aggregate stays within the
  constraint:

      window-valid? window-value limit = decide (window-value <= limit)

  over exact-rational aggregates. Proved native and axiom-free: the window-validity
  test; that a window within the budget is valid (the right edge may keep growing);
  the certificate that a valid window's value really is within the limit (native
  nnrat/at-most); and that a window exceeding the budget is invalid (the left edge
  must shrink). The incremental add/remove of window elements is executable; what
  is proved is the window-validity decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.sliding-window`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- window-valid? [window-value limit]
  (function/app (function/const* 'sliding-window/window-valid? []) window-value limit))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; window-valid? window-value limit = decide (window-value <= limit)
(def window-valid-spec
  {:name 'sliding-window/window-valid? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['window-value nnrat] ['limit nnrat]]
                        (decide-at-most 'window-value 'limit))})

(def definition-specs [window-valid-spec])

;; Theorems -----------------------------------------------------------------

;; A window with value 3 within the limit 5 is valid (grow the right edge).
(def within-budget-valid-spec
  {:name 'sliding-window/within-budget-valid :universes []
   :type (equality bool (window-valid? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (window-valid? (whole 3) (whole 5)))})

;; Certificate: a valid window's value is within the limit (3 <= 5).
(def valid-window-within-limit-spec
  {:name 'sliding-window/valid-window-within-limit :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A window with value 8 exceeding the limit 5 is invalid (shrink the left edge).
(def over-budget-invalid-spec
  {:name 'sliding-window/over-budget-invalid :universes []
   :type (equality bool (window-valid? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (window-valid? (whole 8) (whole 5)))})

(def theorem-specs
  [within-budget-valid-spec valid-window-within-limit-spec
   over-budget-invalid-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-sliding-window (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.sliding-window))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
