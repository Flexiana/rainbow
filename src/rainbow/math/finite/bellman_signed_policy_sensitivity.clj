(ns rainbow.math.finite.bellman-signed-policy-sensitivity
  "Robustness of signed fixed-policy Bellman evaluations under model drift.

  The reference discounted-transition matrix is a canonical rational
  contraction. The comparison matrix need not contract. Two possibly
  approximate value vectors are separated by their own Bellman residuals,
  signed reward-vector distance, and the transition-operator discrepancy at
  the comparison value. The sharp inverse-gap factor turns those independently
  checkable quantities into one value-function sensitivity certificate.

  This is a fixed-policy finite-matrix result, not signed Bellman optimality.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-general-rate-sensitivity
             :as sensitivity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- policy-step [rows reward values]
  (app (function/const* 'matrix/affine-action []) rows reward values))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))
(defn- rate [ap gp]
  (make (succ ap) (nadd ap (succ gp))))
(defn- inverse [ap gp]
  (make (nadd (succ ap) (succ gp)) gp))

(defn- problem-binders []
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image (policy-step 'left-rows 'left-reward 'left)
        right-image (policy-step 'right-rows 'right-reward 'right)]
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-reward vector-type] ['right-reward vector-type]
     ['left vector-type] ['right vector-type]
     ['ap nat] ['gp nat]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['left-reward-shape
      (same-shape 'left-reward (action 'left-rows 'left))]
     ['right-reward-shape
      (same-shape 'right-reward right-action-at-right)]
     ['action-bridge-shape
      (same-shape left-action-at-right right-action-at-right)]
     ['positive-left-rows (rows-positive 'left-rows)]
     ['bounded-left-sums
      (row-sums-bounded
       'left-rows (from-nnrat (rate 'ap 'gp)))]]))

(def signed-policy-problem-perturbation-stability-spec
  (let [left-image (policy-step 'left-rows 'left-reward 'left)
        right-image (policy-step 'right-rows 'right-reward 'right)
        left-residual (sup-distance 'left left-image)
        reward-distance (sup-distance 'left-reward 'right-reward)
        operator-distance
        (sup-distance
         (action 'left-rows 'right)
         (action 'right-rows 'right))
        right-residual (sup-distance right-image 'right)
        aggregate
        (sadd left-residual
              (sadd (sadd reward-distance operator-distance)
                    right-residual))]
    {:name 'bellman/signed-policy-problem-perturbation-stability
     :universes []
     :type
     (function/forall
      (problem-binders)
      (sle
       (sup-distance 'left 'right)
       (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
     :value
     (function/lam
      (problem-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-problem-perturbation-stability [])
       'left-rows 'right-rows 'left-reward 'right-reward 'left 'right
       'ap 'gp
       'shape 'left-residual-shape 'right-residual-shape
       'left-reward-shape 'right-reward-shape 'action-bridge-shape
       'positive-left-rows 'bounded-left-sums))}))

(def definition-specs [])
(def theorem-specs [signed-policy-problem-perturbation-stability-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-general-rate-sensitivity])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-policy-sensitivity theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-policy-sensitivity))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
