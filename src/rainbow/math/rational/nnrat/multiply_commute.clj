(ns rainbow.math.rational.nnrat.multiply-commute
  "Standalone provider of nnrat/multiply-commutative (a*b ~ b*a), extracted so it
  can be chained WITHOUT nnrat_commutative's bundled nnrat/add-commutative, which
  alias-conflicts with nnrat_add_monotone's (different proof/sha).  The proof is
  the same one as in nnrat_commutative: unfold to the cross product and reorder
  numerator and denominator with the native nat commutativity lemmas.  Depends
  only on the d63 base (nnrat accessors, nat/multiply-commutative, nat congruence
  and transitivity).  Native and axiom-free."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- predecessor [value] (function/app (function/const* 'nat/predecessor []) value))
(defn- numerator [value] (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value] (function/app (function/const* 'nnrat/denominator []) value))
(defn- denominator-predecessor [value]
  (function/app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- multiply-nat [left right] (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-multiply [left right] (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equivalent [left right] (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- congr [mapping left right proof]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping left right proof))
(defn- transitive [left middle right p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat left middle right p q))
(defn- nat-multiply-commutative [left right]
  (function/app (function/const* 'nat/multiply-commutative []) left right))

(def multiply-commutative-spec
  {:name 'nnrat/multiply-commutative
   :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
                          (equivalent (nnrat-multiply 'a 'b)
                                      (nnrat-multiply 'b 'a)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [na (numerator 'a) nb (numerator 'b)
          dpa (denominator-predecessor 'a) dpb (denominator-predecessor 'b)
          num-ab (multiply-nat na nb)
          num-ba (multiply-nat nb na)
          den-ab (denominator (nnrat-multiply 'a 'b))
          den-ba (denominator (nnrat-multiply 'b 'a))
          num-comm (nat-multiply-commutative na nb)
          mul-comm (nat-multiply-commutative (succ dpb) (succ dpa))
          pred-comm (congr (function/lam [['m nat]] (predecessor 'm))
                           (multiply-nat (succ dpb) (succ dpa))
                           (multiply-nat (succ dpa) (succ dpb))
                           mul-comm)
          den-comm (congr (function/lam [['c nat]] (succ 'c))
                          (predecessor (multiply-nat (succ dpb) (succ dpa)))
                          (predecessor (multiply-nat (succ dpa) (succ dpb)))
                          pred-comm)
          left-step (congr (function/lam [['x nat]] (multiply-nat 'x den-ba))
                           num-ab num-ba num-comm)
          right-step (congr (function/lam [['d nat]] (multiply-nat num-ba 'd))
                            den-ba den-ab den-comm)]
      (transitive (multiply-nat num-ab den-ba)
                  (multiply-nat num-ba den-ba)
                  (multiply-nat num-ba den-ab)
                  left-step right-step)))})

(def definition-specs [])
(def theorem-specs [multiply-commutative-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nnrat-multiply-commute (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.multiply-commute))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
