(ns rainbow.math.linear.matrix.gram-positive
  "Positive-semidefinite Gram action for native signed matrices.

  Every signed vector has a nonnegative self-dot, without an entrywise sign
  premise.  The checked transpose/action adjoint law identifies the quadratic
  action dot((A^T)(Ax), x) with dot(Ax, Ax), so the Gram quadratic form is
  nonnegative for every vector compatible with A.  This is the exact-rational
  positive-semidefinite bridge needed by least-squares and quadratic OR cones.
  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.positive-multiply :as positive-multiply]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-positive]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- vr [m b s x]
  (app (function/const* 'data/List.rec [t z]) signed m b s x))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))

(def dot-self-nonnegative-spec
  {:name 'vector/dot-self-nonnegative :universes []
   :type
   (function/forall
    [['values vector-type]]
    (sle signed-zero (dot 'values 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [m
          (function/lam
           [['current vector-type]]
           (sle signed-zero (dot 'current 'current)))
          b
          (app (function/const* 'signed/at-most-reflexive [])
               signed-zero)
          s
          (function/lam
           [['head signed] ['tail vector-type] ['ih (app m 'tail)]]
           (let [square (smul 'head 'head)
                 tail-square (dot 'tail 'tail)
                 sum (sadd square tail-square)
                 zero-sum (sadd signed-zero signed-zero)
                 square-order
                 (app
                  (function/const* 'signed/zero-at-most-of-nonnegative [])
                  square
                  (app (function/const* 'signed/square-nonnegative [])
                       'head))
                 sum-order
                 (app (function/const* 'signed/add-monotone [])
                      signed-zero square
                      signed-zero tail-square
                      square-order 'ih)]
             (app
              (function/const* 'signed/at-most-respects-equivalence [])
              zero-sum signed-zero sum sum
              (app (function/const* 'signed/add-zero-right [])
                   signed-zero)
              (app (function/const* 'signed/equivalent-reflexive []) sum)
              sum-order)))]
      (vr m b s 'values)))})

(def gram-action-dot-self-spec
  {:name 'matrix/gram-action-equivalent-dot-self :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (seqv
     (dot (action (transpose 'rows) (action 'rows 'values))
          'values)
     (dot (action 'rows 'values) (action 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [image (action 'rows 'values)]
      (app
       (function/const* 'matrix/vector-action-associative [])
       'rows image 'values
       (app (function/const* 'matrix/vector-multiply-column-shape [])
            'rows 'values)
       'rows-compatible)))})

(def gram-action-nonnegative-spec
  {:name 'matrix/gram-action-nonnegative :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (sle
     signed-zero
     (dot (action (transpose 'rows) (action 'rows 'values))
          'values)))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [image (action 'rows 'values)
          gram
          (dot (action (transpose 'rows) image) 'values)
          self (dot image image)
          gram-self
          (app
           (function/const* 'matrix/gram-action-equivalent-dot-self [])
           'rows 'values 'rows-compatible)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       signed-zero signed-zero self gram
       (app (function/const* 'signed/equivalent-reflexive [])
            signed-zero)
       (app (function/const* 'signed/equivalent-symmetric [])
            gram self gram-self)
       (app (function/const* 'vector/dot-self-nonnegative []) image))))})

(def definition-specs [])
(def theorem-specs
  [dot-self-nonnegative-spec
   gram-action-dot-self-spec
   gram-action-nonnegative-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(defn extend-environment [env]
  (-> env
      positive-multiply/extend-environment
      (extend-specs-if-missing
       :signed-decide-order
       (concat decide/definition-specs decide/theorem-specs))
      (extend-specs-if-missing
       :nnrat-add-monotone add-monotone/theorem-specs)
      (extend-spec-if-missing
       'signed/add-nonnegative :vector-norm-nonnegative
       norm-positive/add-nonnegative-spec)
      (extend-spec-if-missing
       'signed/square-nonnegative :vector-norm-nonnegative
       norm-positive/square-nonnegative-spec)
      (support/extend-with :finite-matrix-gram-positive theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
