(ns rainbow.math.rational.nnrat.farkas-recursion-step
  "Piece (ii) recursion step: one full
  elimination round yields a feasible reduced lower/upper system.

  Composes the two big theorems of the round: eliminate a variable from a
  list of structured cross rows (nnrat/farkas-eliminate-structured gives the
  reduced disjunction system) and partition that into a lower-row list and
  an upper-row list (nnrat/farkas-partition-list-necessary). The result:

    cross conditions hold at w  ->  EXISTS (lowers, uppers) with brick 5b's
    lower fold and brick 4's upper fold both holding at w.

  This is the step the variable-count induction folds: each round consumes a
  structured cross system and produces a feasible (lower, upper) system in
  one fewer variable. The output folds are exactly the shape brick 6's
  cross-product consumes, so successive rounds chain. The full induction
  additionally needs the unified representation that carries each row's block
  structure across all remaining variables (so the next round's cross rows
  are again structured); this step is that recursion's proved core. Native
  proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-reduce-align :as align]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def p2 (product nnrat nnrat))
(def p3 (product nnrat p2))
(def p4 (product nnrat p3))
(def structured (product p4 p4))
(def list-structured
  (function/app (function/const* 'data/List [type-level]) structured))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def pair-lists (product list-a list-a))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- cross-holds [rows w]
  (function/app (function/const* 'nnrat/farkas-bridge-cross-holds []) rows w))
(defn- to-bs [rows]
  (function/app (function/const* 'nnrat/farkas-structured-to-both-sides []) rows))
(defn- eliminate-structured [rows w crosses]
  (function/app (function/const* 'nnrat/farkas-eliminate-structured [])
                rows w crosses))
(defn- partition-list [bs-rows w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-list-necessary [])
                bs-rows w reduced))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied [])
                rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows w))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- goal-pred [w]
  (function/lam
   [['pr pair-lists]]
   (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                (uppers-sat (snd list-a list-a 'pr) w))))
(defn- goal [w]
  (function/app (function/const* 'proposition/existence [type-level])
                pair-lists (goal-pred w)))

(def recursion-step-spec
  {:name 'nnrat/farkas-recursion-step
   :universes []
   :type
   (function/forall
    [['rows list-structured] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (goal 'w))
   :value
   (function/lam
    [['rows list-structured] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (partition-list (to-bs 'rows) 'w
                    (eliminate-structured 'rows 'w 'crosses)))})

(def definition-specs [])
(def theorem-specs [recursion-step-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      align/extend-environment
      partition/extend-environment
      (support/extend-with :nnrat-farkas-recursion-step
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
