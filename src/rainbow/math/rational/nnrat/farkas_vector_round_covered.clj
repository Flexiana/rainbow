(ns rainbow.math.rational.nnrat.farkas-vector-round-covered
  "Covered coefficient-vector round (the vacuity fix, consumer migration): one
  Fourier-Motzkin round on the covering-strengthened partition keystone.

  farkas-vector-round produced the vacuous goal EXISTS (l,u), sat -- inherited
  from farkas-partition-list-necessary. This variant applies
  nnrat/farkas-partition-list-covered instead, so its conclusion carries the
  covering conjunct
    length(l)+length(u) = length(packed-list (descs-bilist lowers uppers))
  and is not empty-satisfiable. Same composition as farkas-vector-round
  (cross-vectors-all-reduced -> adapter-bilist -> partition-fold), only the final
  partition is the covered one.

  This is the round's EXISTENTIAL-vacuity fix and is DIRECTION-NEUTRAL: it is
  independent of the uniform-Feasible collapse (Option 1/2), which lives one
  layer up in step/feasible-step/eliminate and is untouched here. Built
  additively; the original farkas-vector-round and the step/eliminate wiring are
  not disturbed. This proof DEPENDS on the covered keystone (its value applies
  partition-list-covered), so it breaks loudly if the keystone stops holding.
  Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-bilist :as vab]
            [rainbow.math.rational.nnrat.farkas-partition-covered :as covered]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))
(def t1 (product lp lp))
(def t2 (product nnrat t1))
(def t3 (product nnrat t2))
(def t4 (product nnrat t3))
(def t5 (product nnrat t4))
(def t6 (product nnrat t5))
(def desc (product nnrat t6))
(def list-desc (function/app (function/const* 'data/List [type-level]) desc))
(def p2 (product nnrat nnrat))
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def pair-lists (product list-a list-a))
(def nat (function/const* 'data/Nat []))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- len-a [l] (function/app (function/const* 'list/length [type-level]) arow l))
(defn- len-bs [l] (function/app (function/const* 'list/length [type-level]) bs-row l))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- neq [a b] (function/equality type-level nat a b))

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

(defn- lowers-hold [lowers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold []) lowers x1))
(defn- uppers-hold [uppers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold []) uppers x1))
(defn- map-uppers [lst x2]
  (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) lst x2))
(defn- all-reduced [lowers uppers x1 lh uh]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-all-reduced [])
                lowers uppers x1 lh uh))
(defn- adapter-bilist [lowers uppers x1 x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-adapter-bilist [])
                lowers uppers x1 x2 h))
(defn- descs-bilist [lowers uppers]
  (function/app (function/const* 'nnrat/farkas-adapter-descs-bilist []) lowers uppers))
(defn- partition-fold [descs x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-partition-fold []) descs x2 h))
(defn- packed-list [descs]
  (function/app (function/const* 'nnrat/farkas-vector-partition-packed []) descs))
(defn- partition-list-covered [rows w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-list-covered []) rows w reduced))

(def round-covered-spec
  {:name 'nnrat/farkas-vector-round-covered
   :universes []
   :type
   (function/forall
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (goal (packed-list (descs-bilist 'lowers 'uppers)) 'x2))
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (let [reduced (all-reduced (map-uppers 'lowers 'x2) (map-uppers 'uppers 'x2) 'x1 'lh 'uh)
          flat (adapter-bilist 'lowers 'uppers 'x1 'x2 reduced)
          conds (partition-fold (descs-bilist 'lowers 'uppers) 'x2 flat)]
      (partition-list-covered (packed-list (descs-bilist 'lowers 'uppers)) 'x2 conds)))})

(def definition-specs [])
(def theorem-specs [round-covered-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-adapter-bilist rainbow.math.rational.nnrat.farkas-partition-covered])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-round-covered (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-round-covered))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
