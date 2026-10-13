(ns rainbow.math.rational.nnrat.farkas-eliminate-all
  "The over-variable recursion: iterate
  one elimination round over the variable count.

  Every round reduces the number of variables by one: from the proved
  pieces, a feasible constraint system in k+1 variables yields a feasible
  system in k variables (cross-vectors-all-reduced produces the reduced
  system; head-split + the both-sides reduction + the dependent partition
  turn it into the next round's lower/upper constraints -- exactly what
  recursion-step does at the affine-row level). This is the induction that
  folds that step: nnrat/farkas-eliminate-all takes a variable count n, a
  feasibility predicate Feasible : Nat -> Prop, and a step
  (Feasible (k+1) -> Feasible k for every k), and concludes Feasible 0 from
  Feasible n -- eliminate all n variables, leaving the condition on the
  objective value alone.

  Proved by Nat.rec on n: base is the identity Feasible 0 -> Feasible 0;
  the successor applies the step then the induction hypothesis. The concrete
  Feasible and step (built from the round + partition machinery) instantiate
  this to the n-variable LP feasibility induction; the base case Feasible 0
  is the objective bound, and the accumulated witnesses across the steps are
  the dual (piece iii). Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def nat (function/const* 'data/Nat []))
(defn- succ [k] (function/app (function/const* 'data/succ []) k))
(def zero (function/const* 'data/zero []))
(defn- fapp [f x] (function/app f x))

(def eliminate-all-spec
  {:name 'nnrat/farkas-eliminate-all
   :universes []
   :type
   (function/forall
    [['feasible (function/arrow nat 'Prop)]
     ['step (function/forall
             [['k nat]]
             (function/arrow (fapp 'feasible (succ 'k))
                             (fapp 'feasible 'k)))]
     ['n nat]
     ['init (fapp 'feasible 'n)]]
    (fapp 'feasible zero))
   :value
   (function/lam
    [['feasible (function/arrow nat 'Prop)]
     ['step (function/forall
             [['k nat]]
             (function/arrow (fapp 'feasible (succ 'k))
                             (fapp 'feasible 'k)))]
     ['n nat]
     ['init (fapp 'feasible 'n)]]
    (function/app
     (function/app
      (function/const* 'data/Nat.rec [zero-level])
      (function/lam
       [['m nat]]
       (function/arrow (fapp 'feasible 'm) (fapp 'feasible zero)))
      (function/lam
       [['f0 (fapp 'feasible zero)]]
       'f0)
      (function/lam
       [['m nat]
        ['ih (function/arrow (fapp 'feasible 'm) (fapp 'feasible zero))]]
       (function/lam
        [['fsm (fapp 'feasible (succ 'm))]]
        (function/app 'ih (function/app (function/app 'step 'm) 'fsm))))
      'n)
     'init))})

(def definition-specs [])
(def theorem-specs [eliminate-all-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-farkas-eliminate-all
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
