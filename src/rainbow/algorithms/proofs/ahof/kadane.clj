(ns rainbow.algorithms.proofs.ahof.kadane
  "AHoF Kadane's Algorithm: find the maximum-sum contiguous subarray in a single
  O(n) pass. It tracks the best subarray sum ending at the current position; at
  each element it decides whether to EXTEND the previous subarray (if that still
  helps) or RESTART at the current element -- the best-ending-here value is

      best-ending element extended = max(element, extended)

  where extended = previous-best-ending + element; extending wins exactly when the
  extended sum is at least the element alone (i.e. the previous best-ending was
  non-negative):

      extend? extended element = decide (element <= extended)

  over exact-rational (non-negative) values. Proved native and axiom-free: the
  extend/restart decision; that extending wins when it helps; the certificate that
  a chosen extension is at least the element alone (native nnrat/at-most); and that
  a non-helpful extension restarts. The running maximum over positions is
  executable; what is proved is the extend-vs-restart decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kadane`
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

(defn- extend? [extended element]
  (function/app (function/const* 'kadane/extend? []) extended element))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; extend? extended element = decide (element <= extended)
(def extend-spec
  {:name 'kadane/extend? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['extended nnrat] ['element nnrat]]
                        (decide-at-most 'element 'extended))})

(def definition-specs [extend-spec])

;; Theorems -----------------------------------------------------------------

;; Extending (sum 7) beats restarting at the element (5): extend the subarray.
(def extending-helps-spec
  {:name 'kadane/extending-helps :universes []
   :type (equality bool (extend? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (extend? (whole 7) (whole 5)))})

;; Certificate: a chosen extension's sum is at least the element alone (5 <= 7),
;; so the best-ending-here value is the extended sum.
(def extension-at-least-element-spec
  {:name 'kadane/extension-at-least-element :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; When extending (sum 2) does not beat the element (5), restart at the element.
(def restart-when-not-helpful-spec
  {:name 'kadane/restart-when-not-helpful :universes []
   :type (equality bool (extend? (whole 2) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (extend? (whole 2) (whole 5)))})

(def theorem-specs
  [extending-helps-spec extension-at-least-element-spec
   restart-when-not-helpful-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-kadane (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.kadane))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
