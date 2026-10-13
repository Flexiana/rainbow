(ns rainbow.math.rational.nnrat.farkas-vector-round
  "The unified representation, one closed round:
  a feasible coefficient-vector system in k+1 variables yields a feasible
  affine system in k variables.

  This composes the whole coefficient-vector round from its proved pieces.
  Represent the system as next-variable constraints (coeff,(bound,(a2,rest)))
  -- x1 the variable eliminated this round, x2 the next -- mapped to the
  round's list form at x2 (farkas-adapter-map-uppers). Given the lower and
  upper constraints all HOLD at x1 (the k+1 system is feasible at this slice):

    farkas-cross-vectors-all-reduced : the pairwise reduced both-sides vector
      conditions hold (eliminate x1);
    farkas-vector-adapter-bilist     : those become all-input-rows of the
      concatenated per-lower descriptor lists (nested fold -> flat fold);
    farkas-vector-partition-fold     : that becomes farkas-reduced-conditions
      of the packed both-sides data list;
    farkas-partition-list-necessary  : that yields EXISTS (lower-affine-list,
      upper-affine-list) both satisfied at x2.

  nnrat/farkas-vector-round is that four-step composition: the k+1 system's
  feasibility at x1 produces a feasible reduced affine (lower,upper) system at
  x2 -- one Fourier-Motzkin round on the coefficient-vector representation,
  end to end, axiom-free. The remaining capstone re-presents that affine
  output as coefficient vectors (unit-column) so the next round consumes it,
  wires this round into farkas-eliminate-all as the concrete step, and reads
  the dual off the accumulated witnesses. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-bilist :as vab]
            [rainbow.math.rational.nnrat.farkas-partition-list :as plist]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; next-variable constraint list
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))

;; the round's cross-vectors constraint list form
(def tb (product lp nnrat))
(def uc (product nnrat tb))
(def list-c (function/app (function/const* 'data/List [type-level]) uc))

;; descriptor list and packed both-sides list
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

;; affine row + the goal (must match nnrat_farkas_partition_list's goal)
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def pair-lists (product list-a list-a))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- goal-pred [w]
  (function/lam
   [['pr pair-lists]]
   (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                (uppers-sat (snd list-a list-a 'pr) w))))
(defn- goal [w]
  (function/app (function/const* 'proposition/existence [type-level])
                pair-lists (goal-pred w)))

;; the four composed theorems / definitions
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
(defn- partition-list [rows w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-list-necessary []) rows w reduced))

(def round-spec
  {:name 'nnrat/farkas-vector-round
   :universes []
   :type
   (function/forall
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (goal 'x2))
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (let [reduced (all-reduced (map-uppers 'lowers 'x2) (map-uppers 'uppers 'x2) 'x1
                               'lh 'uh)
          flat (adapter-bilist 'lowers 'uppers 'x1 'x2 reduced)
          conds (partition-fold (descs-bilist 'lowers 'uppers) 'x2 flat)]
      (partition-list (packed-list (descs-bilist 'lowers 'uppers)) 'x2 conds)))})

(def definition-specs [])
(def theorem-specs [round-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-adapter-bilist rainbow.math.rational.nnrat.farkas-partition-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-round (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-round))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
