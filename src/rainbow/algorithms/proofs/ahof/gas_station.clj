(ns rainbow.algorithms.proofs.ahof.gas-station
  "AHoF Gas Station (greedy circular tour): around a circle of stations, station i
  provides gas[i] and it costs cost[i] to drive to the next. Determine whether a
  starting station exists from which you can complete the loop (tank never
  negative), and find one, in a single O(n) pass. The elegant fact: a valid start
  EXISTS exactly when total gas covers total cost; and the greedy scan (resetting
  the candidate start whenever the running tank goes negative) finds it. The
  feasibility test is:

      can-complete? total-gas total-cost = decide (total-cost <= total-gas)

  over exact-rational totals. Defined: the feasibility test. Proved native and
  axiom-free, as worked instances: gas 7 with cost 5 is judged completable, gas 3
  with cost 5 is not, and the worked certificate 5 <= 7 (native nnrat/at-most).
  The classical fact that total gas covering total cost is necessary and
  sufficient for a valid start, and the correctness of the greedy scan, are not
  proved here. The running-tank scan that locates the start is executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gas-station`
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

(defn- can-complete? [total-gas total-cost]
  (function/app (function/const* 'gas-station/can-complete? []) total-gas total-cost))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; can-complete? total-gas total-cost = decide (total-cost <= total-gas)
(def can-complete-spec
  {:name 'gas-station/can-complete? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['total-gas nnrat] ['total-cost nnrat]]
                        (decide-at-most 'total-cost 'total-gas))})

(def definition-specs [can-complete-spec])

;; Theorems -----------------------------------------------------------------

;; Total gas 7 covering total cost 5 -> the test judges the tour completable.
(def sufficient-gas-completable-spec
  {:name 'gas-station/sufficient-gas-completable :universes []
   :type (equality bool (can-complete? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (can-complete? (whole 7) (whole 5)))})

;; Worked certificate 5 <= 7.
(def completable-cost-covered-spec
  {:name 'gas-station/completable-cost-covered :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A gas deficit (gas 3 < cost 5) -> the test judges the tour not completable.
(def gas-deficit-impossible-spec
  {:name 'gas-station/gas-deficit-impossible :universes []
   :type (equality bool (can-complete? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (can-complete? (whole 3) (whole 5)))})

(def theorem-specs
  [sufficient-gas-completable-spec completable-cost-covered-spec
   gas-deficit-impossible-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-gas-station (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.gas-station))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
