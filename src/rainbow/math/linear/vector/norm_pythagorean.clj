(ns rainbow.math.linear.vector.norm-pythagorean
  "Pythagoras and order bounds for native signed-rational vectors.

  For same-shaped vectors with zero inner product, the existing four-term norm
  expansion collapses to the exact sum of the two squared norms.  Since every
  self-dot is nonnegative, either summand's squared norm is at most the squared
  norm of the orthogonal sum.  These theorem-only boundaries are the generic
  bridge from Gram positivity to least-squares optimality.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.row-gram-kernel :as row-kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.norm-expansion :as expansion]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))

(defn- app [f & xs] (apply function/app f xs))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- norm2 [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- transitive [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- symmetric [a b same]
  (app (function/const* 'signed/equivalent-symmetric []) a b same))
(defn- zero-left [value]
  (transitive
   (sadd signed-zero value) (sadd value signed-zero) value
   (app (function/const* 'signed/add-commutative [])
        signed-zero value)
   (app (function/const* 'signed/add-zero-right []) value)))

(def norm-squared-add-orthogonal-spec
  {:name 'norm/norm-squared-add-orthogonal :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (seqv
     (norm2 (vadd 'left 'right))
     (sadd (norm2 'left) (norm2 'right))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (let [left2 (norm2 'left)
          right2 (norm2 'right)
          lr (dot 'left 'right)
          rl (dot 'right 'left)
          start (norm2 (vadd 'left 'right))
          expanded (sadd (sadd left2 lr) (sadd rl right2))
          zeroed
          (sadd (sadd left2 signed-zero)
                (sadd signed-zero right2))
          finish (sadd left2 right2)
          reverse-orthogonal
          (transitive
           rl lr signed-zero
           (app (function/const* 'vector/dot-commutative [])
                'right 'left)
           'orthogonal)
          cross-terms-zero
          (app
           (function/const* 'signed/add-respects-equivalence [])
           (sadd left2 lr) (sadd left2 signed-zero)
           (sadd rl right2) (sadd signed-zero right2)
           (app
            (function/const* 'signed/add-respects-equivalence [])
            left2 left2 lr signed-zero
            (app (function/const* 'signed/equivalent-reflexive []) left2)
            'orthogonal)
           (app
            (function/const* 'signed/add-respects-equivalence [])
            rl signed-zero right2 right2
            reverse-orthogonal
            (app (function/const* 'signed/equivalent-reflexive [])
                 right2)))
          zeros-collapse
          (app
           (function/const* 'signed/add-respects-equivalence [])
           (sadd left2 signed-zero) left2
           (sadd signed-zero right2) right2
           (app (function/const* 'signed/add-zero-right []) left2)
           (zero-left right2))]
      (transitive
       start zeroed finish
       (transitive
        start expanded zeroed
        (app (function/const* 'norm/norm-squared-add [])
             'left 'right 'shape)
        cross-terms-zero)
       zeros-collapse)))})

(def norm-squared-left-at-most-orthogonal-sum-spec
  {:name 'norm/norm-squared-left-at-most-orthogonal-sum :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (sle (norm2 'left) (norm2 (vadd 'left 'right))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (let [left2 (norm2 'left)
          right2 (norm2 'right)
          total (norm2 (vadd 'left 'right))
          sum (sadd left2 right2)
          padded (sadd left2 signed-zero)
          right-positive
          (app (function/const* 'signed/zero-at-most-of-nonnegative [])
               right2
               (app (function/const* 'norm/norm-squared-nonnegative [])
                    'right))
          padded-order
          (app (function/const* 'signed/add-left-monotone [])
               signed-zero right2 left2 right-positive)
          total-sum
          (app (function/const* 'norm/norm-squared-add-orthogonal [])
               'left 'right 'shape 'orthogonal)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       padded left2 sum total
       (app (function/const* 'signed/add-zero-right []) left2)
       (symmetric total sum total-sum)
       padded-order)))})

(def norm-squared-right-at-most-orthogonal-sum-spec
  {:name 'norm/norm-squared-right-at-most-orthogonal-sum :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (sle (norm2 'right) (norm2 (vadd 'left 'right))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['orthogonal (seqv (dot 'left 'right) signed-zero)]]
    (let [left2 (norm2 'left)
          right2 (norm2 'right)
          total (norm2 (vadd 'left 'right))
          sum (sadd left2 right2)
          padded (sadd signed-zero right2)
          left-positive
          (app (function/const* 'signed/zero-at-most-of-nonnegative [])
               left2
               (app (function/const* 'norm/norm-squared-nonnegative [])
                    'left))
          padded-order
          (app (function/const* 'signed/add-right-monotone [])
               signed-zero left2 right2 left-positive)
          total-sum
          (app (function/const* 'norm/norm-squared-add-orthogonal [])
               'left 'right 'shape 'orthogonal)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       padded right2 sum total
       (zero-left right2)
       (symmetric total sum total-sum)
       padded-order)))})

(def definition-specs [])
(def theorem-specs
  [norm-squared-add-orthogonal-spec
   norm-squared-left-at-most-orthogonal-sum-spec
   norm-squared-right-at-most-orthogonal-sum-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.row-gram-kernel])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'norm/norm-squared-add :vector-norm-expansion expansion/norm-squared-add-spec) (support/extend-with :vector-norm-pythagorean theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.vector.norm-pythagorean))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
