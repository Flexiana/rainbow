(ns rainbow.math.rational.nnrat.farkas-linear-form
  "The unified representation, brick 1:
  the coefficient-vector (linear-form) constraint type and the head-split
  extraction.

  A constraint over the remaining variables is a list of (coefficient,
  variable) pairs; nnrat/linear-form evaluates it to sum_i c_i*x_i. The
  representation is closed under elimination: the head pair is the current
  variable's (coefficient, value) and the tail is the block over the
  remaining variables. nnrat/linear-form-upper-split and -lower-split expose
  exactly that -- an upper constraint eval(cons p tail) <= b holds iff
  fst(p)*snd(p) + eval(tail) <= b (and the lower analogue), because
  eval(cons p tail) reduces definitionally to fst(p)*snd(p) + eval(tail).
  So a coefficient-vector row presents as the structured affine row the
  elimination round consumes, with block = eval(tail) (itself affine in the
  next variable, its head). The columnwise cross transform over these vectors
  is brick 2. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nn
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
(def list-pair
  (function/app (function/const* 'data/List [type-level]) pair-nn))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(def zero (function/const* 'nnrat/zero []))
(defn- fst [v]
  (function/app (function/const* 'product/first [type-level type-level])
                nnrat nnrat v))
(defn- snd [v]
  (function/app (function/const* 'product/second [type-level type-level])
                nnrat nnrat v))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- eval-form [pairs]
  (function/app (function/const* 'nnrat/linear-form []) pairs))

;; eval a coefficient-vector: sum of coefficient * variable over the pairs
(def linear-form-spec
  {:name 'nnrat/linear-form
   :kind :definition
   :universes []
   :type (function/arrow list-pair nnrat)
   :value
   (function/lam
    [['pairs list-pair]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     pair-nn
     (function/lam [['ignored list-pair]] nnrat)
     zero
     (function/lam
      [['head pair-nn] ['tail list-pair] ['ih nnrat]]
      (add (mul (fst 'head) (snd 'head)) 'ih))
     'pairs))})

(def definition-specs [linear-form-spec])

;; an upper constraint on a coefficient-vector row splits off the head
;; variable: eval(cons p tail) <= b  =>  fst(p)*snd(p) + eval(tail) <= b.
;; (eval(cons ...) reduces to exactly that, so the proof is the hypothesis.)
(def upper-split-spec
  {:name 'nnrat/linear-form-upper-split
   :universes []
   :type
   (function/forall
    [['p pair-nn] ['tail list-pair] ['b nnrat]
     ['h (at-most (eval-form (cons-pair 'p 'tail)) 'b)]]
    (at-most (add (mul (fst 'p) (snd 'p)) (eval-form 'tail)) 'b))
   :value
   (function/lam
    [['p pair-nn] ['tail list-pair] ['b nnrat]
     ['h (at-most (eval-form (cons-pair 'p 'tail)) 'b)]]
    'h)})

;; the lower analogue: w <= eval(cons p tail)  =>  w <= fst(p)*snd(p) + eval(tail)
(def lower-split-spec
  {:name 'nnrat/linear-form-lower-split
   :universes []
   :type
   (function/forall
    [['w nnrat] ['p pair-nn] ['tail list-pair]
     ['h (at-most 'w (eval-form (cons-pair 'p 'tail)))]]
    (at-most 'w (add (mul (fst 'p) (snd 'p)) (eval-form 'tail))))
   :value
   (function/lam
    [['w nnrat] ['p pair-nn] ['tail list-pair]
     ['h (at-most 'w (eval-form (cons-pair 'p 'tail)))]]
    'h)})

(def theorem-specs [upper-split-spec lower-split-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-farkas-linear-form
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
