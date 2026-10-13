(ns rainbow.math.rational.nnrat.farkas-row-repackage
  "Brick 5a of the general LP strong-duality Fourier-Motzkin encoding
 : the row-repackaging crux, the one
  genuinely new proof obligation of the strong-duality payoff.

  Chaining eliminations (eliminate x1, feed the reduced system into x2's
  elimination) needs brick 4's reduced row -- at x1 = max-lb1, an affine
  row with survivor block c*w + d reads a*max-lb1 + (c*w + d) <= b -- to be
  re-presented as a FRESH brick-4 row in the next variable w:
  c*w + (a*max-lb1 + d) <= b. The two couplings differ only by
  reassociating m + (cw + d) into cw + (m + d), where m = a*max-lb1. In
  nnrat that reassociation is an EQUIVALENCE (~), not propositional
  equality -- the subtlety the whole LP layer works around -- so the <= is
  transported across it with nnrat/at-most-respects-equivalence, the ~
  itself supplied by nnrat/add-swap-right (p + (q + r) ~ q + (p + r)).

  nnrat/farkas-row-repackage-iff states the equivalence of the two coupling
  forms, both directions, for all operands. It is deliberately the pure
  per-row content (no row types, no list) -- the reusable heart that
  brick 5c maps over a row list to chain the two-variable elimination.
  Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as reassoc]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- add-swap-right [a b c]
  (function/app (function/const* 'nnrat/add-swap-right []) a b c))
(defn- at-most-respects [left eq-left right eq-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left eq-left right eq-right same-left same-right ordered))

;; The two coupling forms, in a*m + (c*w + d) shape (the eliminated
;; variable's contribution m = a*max-lb is grouped first) and the
;; repackaged c*w + (a*m + d) shape (a fresh brick-4 row in w).
(defn- eliminated [a m c w d]
  (add (multiply a m) (add (multiply c w) d)))
(defn- repackaged [a m c w d]
  (add (multiply c w) (add (multiply a m) d)))

(def repackage-iff-spec
  {:name 'nnrat/farkas-row-repackage-iff
   :universes []
   :type
   (function/forall
    [['a nnrat] ['m nnrat] ['c nnrat] ['w nnrat] ['d nnrat] ['b nnrat]]
    (proposition/equivalence
     (at-most (eliminated 'a 'm 'c 'w 'd) 'b)
     (at-most (repackaged 'a 'm 'c 'w 'd) 'b)))
   :value
   (function/lam
    [['a nnrat] ['m nnrat] ['c nnrat] ['w nnrat] ['d nnrat] ['b nnrat]]
    (let [x (eliminated 'a 'm 'c 'w 'd)      ; a*m + (c*w + d)
          x' (repackaged 'a 'm 'c 'w 'd)     ; c*w + (a*m + d)
          ;; x' ~ x  and  x ~ x', each one add-swap-right.
          x'-eq-x (add-swap-right (multiply 'c 'w) (multiply 'a 'm) 'd)
          x-eq-x' (add-swap-right (multiply 'a 'm) (multiply 'c 'w) 'd)
          b-refl (equivalent-reflexive 'b)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       (at-most x 'b) (at-most x' 'b)
       ;; forward: x <= b  =>  x' <= b
       (function/lam
        [['ordered (at-most x 'b)]]
        (at-most-respects x' x 'b 'b x'-eq-x b-refl 'ordered))
       ;; backward: x' <= b  =>  x <= b
       (function/lam
        [['ordered (at-most x' 'b)]]
        (at-most-respects x x' 'b 'b x-eq-x' b-refl 'ordered)))))})

(def definition-specs [])
(def theorem-specs [repackage-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.additive-reassociation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-row-repackage (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-row-repackage))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
