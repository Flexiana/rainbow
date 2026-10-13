(ns rainbow.math.linear.matrix.least-squares-equality
  "Equality and nullspace directions in exact finite least squares.

  Signed additive equivalence cancellation is derived from the existing order
  cancellation laws and antisymmetry.  Applying it to the normal-residual
  Pythagorean identity proves that the affine least-squares objective equals its
  normal residual value exactly when A d is componentwise zero.  Thus normal
  solutions are unique modulo ker A, with all finite row-list shape premises
  explicit.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.least-squares-normal :as normal]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order-cancellation :as order-cancellation]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- vz [values] (app (function/const* 'vector/zero-like []) values))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- norm2 [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- transitive [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- symmetric [a b same]
  (app (function/const* 'signed/equivalent-symmetric []) a b same))

(def equivalent-add-right-cancel-spec
  {:name 'signed/equivalent-add-right-cancel :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['offset signed]
     ['same
      (seqv (sadd 'left 'offset) (sadd 'right 'offset))]]
    (seqv 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed] ['offset signed]
     ['same
      (seqv (sadd 'left 'offset) (sadd 'right 'offset))]]
    (let [left-right
          (app (function/const* 'signed/at-most-add-right-cancel [])
               'left 'right 'offset
               (app (function/const* 'signed/equivalent-to-at-most [])
                    (sadd 'left 'offset) (sadd 'right 'offset) 'same))
          right-left
          (app (function/const* 'signed/at-most-add-right-cancel [])
               'right 'left 'offset
               (app
                (function/const* 'signed/equivalent-to-at-most [])
                (sadd 'right 'offset) (sadd 'left 'offset)
                (symmetric (sadd 'left 'offset)
                           (sadd 'right 'offset) 'same)))]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'left 'right left-right right-left)))})

(def equivalent-add-left-cancel-spec
  {:name 'signed/equivalent-add-left-cancel :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['offset signed]
     ['same
      (seqv (sadd 'offset 'left) (sadd 'offset 'right))]]
    (seqv 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed] ['offset signed]
     ['same
      (seqv (sadd 'offset 'left) (sadd 'offset 'right))]]
    (let [left-right
          (app (function/const* 'signed/at-most-add-left-cancel [])
               'left 'right 'offset
               (app (function/const* 'signed/equivalent-to-at-most [])
                    (sadd 'offset 'left) (sadd 'offset 'right) 'same))
          right-left
          (app (function/const* 'signed/at-most-add-left-cancel [])
               'right 'left 'offset
               (app
                (function/const* 'signed/equivalent-to-at-most [])
                (sadd 'offset 'right) (sadd 'offset 'left)
                (symmetric (sadd 'offset 'left)
                           (sadd 'offset 'right) 'same)))]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'left 'right left-right right-left)))})

(def normal-affine-equal-of-null-direction-spec
  {:name 'matrix/normal-affine-equal-of-null-direction :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]
     ['direction-null
      (let [image (action 'rows 'direction)]
        (veq image (vz image)))]]
    (let [image (action 'rows 'direction)]
      (seqv (norm2 (vadd 'residual image))
            (norm2 'residual))))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]
     ['direction-null
      (let [image (action 'rows 'direction)]
        (veq image (vz image)))]]
    (let [image (action 'rows 'direction)
          residual2 (norm2 'residual)
          image2 (norm2 image)
          total (norm2 (vadd 'residual image))
          sum (sadd residual2 image2)
          zero-sum (sadd residual2 signed-zero)
          pythagoras
          (app
           (function/const* 'matrix/normal-residual-affine-pythagorean [])
           'rows 'residual 'direction
           'residual-shape 'direction-compatible 'transpose-null)
          image-zero
          (app
           (function/const*
            'vector/dot-self-zero-of-equivalent-zero-like [])
           image 'direction-null)
          sum-zero
          (app
           (function/const* 'signed/add-respects-equivalence [])
           residual2 residual2 image2 signed-zero
           (app (function/const* 'signed/equivalent-reflexive [])
                residual2)
           image-zero)]
      (transitive
       total zero-sum residual2
       (transitive total sum zero-sum pythagoras sum-zero)
       (app (function/const* 'signed/add-zero-right []) residual2))))})

(def normal-affine-equal-reflects-null-direction-spec
  {:name 'matrix/normal-affine-equal-reflects-null-direction :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]
     ['objective-equal
      (let [image (action 'rows 'direction)]
        (seqv (norm2 (vadd 'residual image))
              (norm2 'residual)))]]
    (let [image (action 'rows 'direction)]
      (veq image (vz image))))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]
     ['objective-equal
      (let [image (action 'rows 'direction)]
        (seqv (norm2 (vadd 'residual image))
              (norm2 'residual)))]]
    (let [image (action 'rows 'direction)
          residual2 (norm2 'residual)
          image2 (norm2 image)
          total (norm2 (vadd 'residual image))
          sum (sadd residual2 image2)
          zero-sum (sadd residual2 signed-zero)
          pythagoras
          (app
           (function/const* 'matrix/normal-residual-affine-pythagorean [])
           'rows 'residual 'direction
           'residual-shape 'direction-compatible 'transpose-null)
          sum-zero-sum
          (transitive
           sum residual2 zero-sum
           (transitive sum total residual2
                       (symmetric total sum pythagoras)
                       'objective-equal)
           (symmetric zero-sum residual2
                      (app (function/const* 'signed/add-zero-right [])
                           residual2)))
          image-zero
          (app (function/const* 'signed/equivalent-add-left-cancel [])
               image2 signed-zero residual2 sum-zero-sum)]
      (app (function/const* 'vector/dot-self-zero-reflects [])
           image image-zero)))})

(def normal-affine-equality-characterizes-null-direction-spec
  {:name 'matrix/normal-affine-equality-characterizes-null-direction
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]]
    (let [image (action 'rows 'direction)
          objective-equal
          (seqv (norm2 (vadd 'residual image)) (norm2 'residual))
          direction-null (veq image (vz image))]
      (app (function/const* 'proposition/conjunction [])
           (function/arrow objective-equal direction-null)
           (function/arrow direction-null objective-equal))))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal-image (action (transpose 'rows) 'residual)]
        (veq normal-image (vz normal-image)))]]
    (let [image (action 'rows 'direction)
          objective-equal
          (seqv (norm2 (vadd 'residual image)) (norm2 'residual))
          direction-null (veq image (vz image))]
      (conjp
       (function/arrow objective-equal direction-null)
       (function/arrow direction-null objective-equal)
       (function/lam
        [['same-proof objective-equal]]
        (app
         (function/const*
          'matrix/normal-affine-equal-reflects-null-direction [])
         'rows 'residual 'direction
         'residual-shape 'direction-compatible 'transpose-null
         'same-proof))
       (function/lam
        [['null-proof direction-null]]
        (app
         (function/const* 'matrix/normal-affine-equal-of-null-direction [])
         'rows 'residual 'direction
         'residual-shape 'direction-compatible 'transpose-null
         'null-proof)))))})

(def definition-specs [])
(def theorem-specs
  [equivalent-add-right-cancel-spec
   equivalent-add-left-cancel-spec
   normal-affine-equal-of-null-direction-spec
   normal-affine-equal-reflects-null-direction-spec
   normal-affine-equality-characterizes-null-direction-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.least-squares-normal])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/at-most-add-right-cancel :signed-order-cancellation order-cancellation/add-right-cancel-spec) (extend-spec-if-missing 'signed/at-most-add-left-cancel :signed-order-cancellation order-cancellation/add-left-cancel-spec) (support/extend-with :finite-matrix-least-squares-equality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.least-squares-equality))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
