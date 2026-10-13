(ns rainbow.math.rational.nnrat.farkas-vector-unit-repr-length
  "Length preservation of the unit-column re-presentation map (support for the
  covered step migration).

  farkas-vector-unit-repr maps an affine-row list to a next-variable-constraint
  list, one output entry per input entry. So it preserves length:
    length(farkas-vector-unit-repr rows) = length(rows).
  The covered step needs this to carry the covering conjunct from the round's
  affine lists (length l + length u = length(packed rows)) onto the re-presented
  nvc lists. Proof: List.rec on rows -- nil is reflexivity (both 0), cons is one
  succ-congruence (repr's cons and length's cons both prepend one). Native proof
  data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-vector-unit-column :as unit-column]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))
(def p2 (product nnrat nnrat))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def nat (function/const* 'data/Nat []))

(defn- unit-repr [rows]
  (function/app (function/const* 'nnrat/farkas-vector-unit-repr []) rows))
(defn- len-a [l] (function/app (function/const* 'list/length [type-level]) arow l))
(defn- len-nvc [l] (function/app (function/const* 'list/length [type-level]) nvc l))
(defn- neq [a b] (function/equality type-level nat a b))
(defn- refl-nat [a] (function/app (function/const* 'equality/reflexive [type-level]) nat a))
(def succ-fn (function/lam [['n nat]] (function/app (function/const* 'data/succ []) 'n)))
(defn- congr-succ [a b h]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat succ-fn a b h))
(defn- cons-a [h t] (function/app (function/const* 'data/cons [type-level]) arow h t))
(def nil-a (function/app (function/const* 'data/nil [type-level]) arow))

(def repr-length-spec
  {:name 'nnrat/farkas-vector-unit-repr-length
   :universes []
   :type
   (function/forall
    [['rows list-a]]
    (neq (len-nvc (unit-repr 'rows)) (len-a 'rows)))
   :value
   (function/lam
    [['rows list-a]]
    (function/app
     (function/const* 'data/List.rec [type-level zero-level])
     arow
     (function/lam [['rs list-a]] (neq (len-nvc (unit-repr 'rs)) (len-a 'rs)))
     ;; nil: length(repr nil) = 0 = length nil
     (refl-nat (len-nvc (unit-repr nil-a)))
     ;; cons head tail: succ-congruence on the induction hypothesis
     (function/lam
      [['head arow] ['tail list-a]
       ['ih (neq (len-nvc (unit-repr 'tail)) (len-a 'tail))]]
      (congr-succ (len-nvc (unit-repr 'tail)) (len-a 'tail) 'ih))
     'rows))})

(def definition-specs [])
(def theorem-specs [repr-length-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      unit-column/extend-environment
      (support/extend-with :nnrat-farkas-vector-unit-repr-length
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
