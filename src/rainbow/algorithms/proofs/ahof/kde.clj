(ns rainbow.algorithms.proofs.ahof.kde
  "AHoF D12 Nonparametric Learning (Kernel Density Estimation): estimate a density as
  a sum of kernels centered at the data points, each with bandwidth h. What is defined
  here is only a closed bandwidth-WINDOW decision, true when a point's distance from the
  query is at most the bandwidth:

      in-bandwidth? distance bandwidth = decide (distance <= bandwidth).

  Whether a point inside the window actually contributes depends on the kernel and its
  support, which are not modelled here: for the triangular kernel K(u)=max(0,1-abs(u))
  a point at distance equal to the bandwidth passes the window test but contributes
  zero. Proved native and axiom-free, as worked instances: distance 1/2 with bandwidth
  3/4 is in the window, the certificate 1/2 <= 3/4, and distance 3/4 with bandwidth 1/2
  is outside it. Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kde`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- in-bandwidth? [distance bandwidth]
  (function/app (function/const* 'kde/in-bandwidth? []) distance bandwidth))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def in-bandwidth-spec
  {:name 'kde/in-bandwidth? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['distance nnrat] ['bandwidth nnrat]]
                        (decide-at-most 'distance 'bandwidth))})

(def definition-specs [in-bandwidth-spec])

(def within-window-contributes-spec
  {:name 'kde/within-window-contributes :universes []
   :type (equality bool (in-bandwidth? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-bandwidth? (fraction 1 1) (fraction 3 3)))})

(def support-certificate-spec
  {:name 'kde/support-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def outside-window-excluded-spec
  {:name 'kde/outside-window-excluded :universes []
   :type (equality bool (in-bandwidth? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-bandwidth? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [within-window-contributes-spec support-certificate-spec
   outside-window-excluded-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-kde
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
