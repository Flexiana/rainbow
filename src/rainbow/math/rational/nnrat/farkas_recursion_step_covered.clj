(ns rainbow.math.rational.nnrat.farkas-recursion-step-covered
  "Covered recursion step (the vacuity fix, consumer migration): the affine
  elimination round built on the COVERING-strengthened partition keystone.

  farkas-recursion-step produced the vacuous goal EXISTS (l,u), sat -- inherited
  from farkas-partition-list-necessary. This variant, farkas-recursion-step-
  covered, is the identical composition but applies
  nnrat/farkas-partition-list-covered instead, so its conclusion carries the
  covering conjunct length(l)+length(u)=length(to-bs rows) and is therefore NOT
  empty-satisfiable. It is the first consumer migrated onto the strengthened
  keystone.

  The point of the exercise (the vacuity lesson): this proof DEPENDS on the
  covered keystone -- its value is exactly partition-list-covered applied to the
  eliminated structured rows -- so if the keystone stopped holding, this proof
  breaks loudly rather than silently falling back to a weaker fact. A dependency
  guard in the test asserts the proof value mentions farkas-partition-list-
  covered. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-reduce-align :as align]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition]
            [rainbow.math.rational.nnrat.farkas-partition-covered :as covered]))

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
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))
(def nat (function/const* 'data/Nat []))

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
(defn- partition-list-covered [bs-rows w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-list-covered [])
                bs-rows w reduced))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- len-a [l] (function/app (function/const* 'list/length [type-level]) arow l))
(defn- len-bs [l] (function/app (function/const* 'list/length [type-level]) bs-row l))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- neq [a b] (function/equality type-level nat a b))

;; the covered goal (identical to farkas-partition-list-covered's goal, over
;; rs = to-bs rows): EXISTS (l,u), (sat-l /\ sat-u) /\ len(l)+len(u) = len rs
(defn- goal-pred [rs w]
  (function/lam
   [['pr pair-lists]]
   (conjunction (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                             (uppers-sat (snd list-a list-a 'pr) w))
                (neq (nadd (len-a (fst list-a list-a 'pr)) (len-a (snd list-a list-a 'pr)))
                     (len-bs rs)))))
(defn- goal [rs w]
  (function/app (function/const* 'proposition/existence [type-level])
                pair-lists (goal-pred rs w)))

(def recursion-step-covered-spec
  {:name 'nnrat/farkas-recursion-step-covered
   :universes []
   :type
   (function/forall
    [['rows list-structured] ['w nnrat] ['crosses (cross-holds 'rows 'w)]]
    (goal (to-bs 'rows) 'w))
   :value
   (function/lam
    [['rows list-structured] ['w nnrat] ['crosses (cross-holds 'rows 'w)]]
    (partition-list-covered (to-bs 'rows) 'w
                            (eliminate-structured 'rows 'w 'crosses)))})

(def definition-specs [])
(def theorem-specs [recursion-step-covered-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-reduce-align rainbow.math.rational.nnrat.farkas-partition-list rainbow.math.rational.nnrat.farkas-partition-covered])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-recursion-step-covered (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-recursion-step-covered))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
