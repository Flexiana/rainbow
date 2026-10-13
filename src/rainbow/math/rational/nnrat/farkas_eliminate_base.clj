(ns rainbow.math.rational.nnrat.farkas-eliminate-base
  "The over-variable recursion's base case:
  a fully-reduced constraint is a constant comparison.

  After all variables are eliminated, a both-sides constraint has empty
  coefficient vectors: eval(nil) + c_L <= eval(nil) + c_R. Since
  nnrat/linear-form evaluates the empty vector to zero (definitionally, its
  List.rec nil case), this is 0 + c_L <= 0 + c_R, which
  nnrat/farkas-eliminate-base reduces to c_L <= c_R -- the condition on the
  constants alone (the objective value against the accumulated dual bound).
  This is Feasible 0 in the eliminate-all induction: the base the recursion
  bottoms out at. Proof: the empty linear form is zero by definition and
  0 + x ~ x (add-zero-left), transported by at-most-respects. Native proof
  data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-linear-form :as linear-form]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nn
  (function/app (function/const* 'data/Product [type-level type-level]) nnrat nnrat))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(def zero (function/const* 'nnrat/zero []))
(defn- eval-form [pairs]
  (function/app (function/const* 'nnrat/linear-form []) pairs))
(def nil-pairs
  (function/app (function/const* 'data/nil [type-level]) pair-nn))
(defn- esym [l r same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- add-zero-left [x]
  (function/app (function/const* 'nnrat/add-zero-left []) x))
(defn- at-most-respects [l el r er sl sr ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                l el r er sl sr ordered))

(def eliminate-base-spec
  {:name 'nnrat/farkas-eliminate-base
   :universes []
   :type
   (function/forall
    [['c-l nnrat] ['c-r nnrat]
     ['h (at-most (add (eval-form nil-pairs) 'c-l)
                  (add (eval-form nil-pairs) 'c-r))]]
    (at-most 'c-l 'c-r))
   :value
   (function/lam
    [['c-l nnrat] ['c-r nnrat]
     ['h (at-most (add (eval-form nil-pairs) 'c-l)
                  (add (eval-form nil-pairs) 'c-r))]]
    ;; h : at-most (0 + c_L) (0 + c_R) after eval(nil) reduces to zero;
    ;; transport both endpoints across 0 + x ~ x.
    (at-most-respects
     'c-l (add zero 'c-l) 'c-r (add zero 'c-r)
     (esym (add zero 'c-l) 'c-l (add-zero-left 'c-l))
     (esym (add zero 'c-r) 'c-r (add-zero-left 'c-r))
     'h))})

(def definition-specs [])
(def theorem-specs [eliminate-base-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      linear-form/extend-environment
      identities/extend-environment
      (support/extend-with :nnrat-farkas-eliminate-base
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
