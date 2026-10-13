(ns rainbow.math.linear.matrix.least-squares-normal
  "Normal-equation sufficiency for exact finite least squares.

  If a residual r has the output shape of A and A^T r is componentwise zero,
  adjointness makes r orthogonal to every compatible image A d.  Pythagoras then
  gives the exact affine decomposition

      ||r + A d||^2 = ||r||^2 + ||A d||^2

  and hence ||r||^2 <= ||r + A d||^2.  This is the native exact-rational
  normal-equation optimality theorem, with all row-list shape assumptions
  explicit.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.norm-pythagorean :as pythagorean]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
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
(defn- transitive [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- symmetric [a b same]
  (app (function/const* 'signed/equivalent-symmetric []) a b same))
(defn- shape-symmetric [a b same]
  (app (function/const* 'vector/same-shape-symmetric []) a b same))
(defn- shape-transitive [a b c ab bc]
  (app (function/const* 'vector/same-shape-transitive []) a b c ab bc))

(def transpose-null-orthogonal-image-spec
  {:name 'matrix/transpose-null-orthogonal-image :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (seqv (dot 'residual (action 'rows 'direction)) signed-zero))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (let [normal (action (transpose 'rows) 'residual)
          image (action 'rows 'direction)
          normal-dot (dot normal 'direction)
          residual-dot (dot 'residual image)
          normal-dot-zero
          (transitive
           normal-dot (dot (vz normal) 'direction) signed-zero
           (app (function/const* 'vector/dot-left-respects-equivalence [])
                normal (vz normal) 'direction 'transpose-null)
           (app (function/const* 'vector/dot-zero-like-left [])
                normal 'direction))
          adjoint
          (app (function/const* 'matrix/vector-action-associative [])
               'rows 'residual 'direction
               'residual-shape 'direction-compatible)]
      (transitive residual-dot normal-dot signed-zero
                  (symmetric normal-dot residual-dot adjoint)
                  normal-dot-zero)))})

(def normal-residual-affine-pythagorean-spec
  {:name 'matrix/normal-residual-affine-pythagorean :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (let [image (action 'rows 'direction)]
      (seqv
       (norm2 (vadd 'residual image))
       (sadd (norm2 'residual) (norm2 image)))))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (let [image (action 'rows 'direction)
          image-shape
          (app (function/const* 'matrix/vector-multiply-column-shape [])
               'rows 'direction)
          residual-image-shape
          (shape-transitive
           'residual (column-shape 'rows) image
           'residual-shape
           (shape-symmetric image (column-shape 'rows) image-shape))
          orthogonal
          (app (function/const* 'matrix/transpose-null-orthogonal-image [])
               'rows 'residual 'direction
               'residual-shape 'direction-compatible 'transpose-null)]
      (app (function/const* 'norm/norm-squared-add-orthogonal [])
           'residual image residual-image-shape orthogonal)))})

(def normal-residual-affine-optimal-spec
  {:name 'matrix/normal-residual-affine-optimal :universes []
   :type
   (function/forall
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (let [image (action 'rows 'direction)]
      (sle (norm2 'residual)
           (norm2 (vadd 'residual image)))))
   :value
   (function/lam
    [['rows matrix-type] ['residual vector-type] ['direction vector-type]
     ['residual-shape
      (same-shape 'residual (column-shape 'rows))]
     ['direction-compatible (compatible 'rows 'direction)]
     ['transpose-null
      (let [normal (action (transpose 'rows) 'residual)]
        (veq normal (vz normal)))]]
    (let [image (action 'rows 'direction)
          image-shape
          (app (function/const* 'matrix/vector-multiply-column-shape [])
               'rows 'direction)
          residual-image-shape
          (shape-transitive
           'residual (column-shape 'rows) image
           'residual-shape
           (shape-symmetric image (column-shape 'rows) image-shape))
          orthogonal
          (app (function/const* 'matrix/transpose-null-orthogonal-image [])
               'rows 'residual 'direction
               'residual-shape 'direction-compatible 'transpose-null)]
      (app
       (function/const*
        'norm/norm-squared-left-at-most-orthogonal-sum [])
       'residual image residual-image-shape orthogonal)))})

(def definition-specs [])
(def theorem-specs
  [transpose-null-orthogonal-image-spec
   normal-residual-affine-pythagorean-spec
   normal-residual-affine-optimal-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.norm-pythagorean])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-least-squares-normal theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.least-squares-normal))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
