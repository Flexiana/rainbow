(ns rainbow.algorithms.proofs.ahof.dual-simplex
  "AHoF O55 Dual Simplex Method: solve a linear program by maintaining DUAL
  feasibility (reduced costs of the right sign) while iterating toward primal
  feasibility. Each pivot picks a leaving variable with negative basic value,
  then chooses the entering variable by the dual RATIO TEST: among eligible
  columns, take the one with the minimum ratio, which preserves dual feasibility.
  Selecting between two candidate columns by ratio is:

      choose-entering ra ia rb ib = if ra <= rb then ia else ib

  over exact-rational ratios (returning the chosen column index). Proved native
  and axiom-free: the ratio-test selection; a worked pivot picking the
  smaller-ratio column; and the certificate that the chosen ratio really is the
  minimum of the two (chosen <= other as native nnrat/at-most), so dual
  feasibility is maintained. The tableau update and eligibility screen are
  executable; what is proved is the dual ratio-test selection.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.dual-simplex`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- choose-entering [ra ia rb ib]
  (function/app (function/const* 'dual-simplex/choose-entering []) ra ia rb ib))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; choose-entering ra ia rb ib = if ra <= rb then ia else ib (min-ratio column)
(def choose-entering-spec
  {:name 'dual-simplex/choose-entering :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['ra nnrat] ['ia nat] ['rb nnrat] ['ib nat]]
                        (if-nat (decide-at-most 'ra 'rb) 'ia 'ib))})

(def definition-specs [choose-entering-spec])

;; Theorems -----------------------------------------------------------------

;; Column 1 has the smaller ratio (1/2 < 3/2), so the pivot enters column 1.
(def enters-min-ratio-column-spec
  {:name 'dual-simplex/enters-min-ratio-column :universes []
   :type (equality nat
                   (choose-entering (fraction 3 1) (data-nat 0)
                                    (fraction 1 1) (data-nat 1))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (choose-entering (fraction 3 1) (data-nat 0)
                                         (fraction 1 1) (data-nat 1)))})

;; When column 0 has the smaller ratio, the pivot enters column 0.
(def enters-first-when-smaller-spec
  {:name 'dual-simplex/enters-first-when-smaller :universes []
   :type (equality nat
                   (choose-entering (fraction 1 3) (data-nat 0)
                                    (fraction 3 3) (data-nat 1))
                   (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (choose-entering (fraction 1 3) (data-nat 0)
                                         (fraction 3 3) (data-nat 1)))})

;; Certificate: the chosen (smaller) ratio 1/2 is at most the other 3/2, so dual
;; feasibility is maintained.
(def chosen-ratio-is-minimal-spec
  {:name 'dual-simplex/chosen-ratio-is-minimal :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 1))
   :value (at-most-proof (fraction 1 1) (fraction 3 1))})

(def theorem-specs
  [enters-min-ratio-column-spec enters-first-when-smaller-spec
   chosen-ratio-is-minimal-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-dual-simplex
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
