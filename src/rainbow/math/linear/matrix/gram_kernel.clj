(ns rainbow.math.linear.matrix.gram-kernel
  "The zero kernel of the native Gram quadratic form.

  A signed vector has zero self-dot exactly when it is componentwise equivalent
  to its shape-preserving zero vector.  Combining this reflection with the Gram
  identity proves both directions between a zero Gram quadratic and Ax being
  zero, then packages them as one conjunction of implications.  Dependency
  activation reuses the existing norm-zero development conditionally, avoiding
  competing aliases.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.gram-positive :as gram-positive]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancel-zero :as add-cancel]
            [rainbow.math.rational.nnrat.add-zero-split :as zero-split]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.quadratic-zero :as quadratic]
            [rainbow.math.rational.signed.add-zero-reflection :as add-reflection]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.square-zero :as square-zero]
            [rainbow.math.linear.vector.additive-units :as units]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]
            [rainbow.math.linear.vector.norm :as norm]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-positive]
            [rainbow.math.linear.vector.norm-zero-reflection :as reflection]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- vz [values] (app (function/const* 'vector/zero-like []) values))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
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

(def dot-self-zero-of-equivalent-zero-like-spec
  {:name 'vector/dot-self-zero-of-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]
     ['zero-equivalent (veq 'values (vz 'values))]]
    (seqv (dot 'values 'values) signed-zero))
   :value
   (function/lam
    [['values vector-type]
     ['zero-equivalent (veq 'values (vz 'values))]]
    (transitive
     (dot 'values 'values)
     (dot (vz 'values) 'values)
     signed-zero
     (app (function/const* 'vector/dot-left-respects-equivalence [])
          'values (vz 'values) 'values 'zero-equivalent)
     (app (function/const* 'vector/dot-zero-like-left [])
          'values 'values)))})

(def dot-self-zero-reflects-spec
  {:name 'vector/dot-self-zero-reflects :universes []
   :type
   (function/forall
    [['values vector-type]
     ['self-zero (seqv (dot 'values 'values) signed-zero)]]
    (veq 'values (vz 'values)))
   :value
   (function/lam
    [['values vector-type]
     ['self-zero (seqv (dot 'values 'values) signed-zero)]]
    (app
     (function/const*
      'norm/equivalent-zero-like-of-norm-squared-zero [])
     'values 'self-zero))})

(def gram-action-zero-of-null-spec
  {:name 'matrix/gram-action-zero-of-null :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]
     ['image-zero
      (veq (action 'rows 'values) (vz (action 'rows 'values)))]]
    (seqv
     (dot (action (transpose 'rows) (action 'rows 'values))
          'values)
     signed-zero))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]
     ['image-zero
      (veq (action 'rows 'values) (vz (action 'rows 'values)))]]
    (let [image (action 'rows 'values)
          gram (dot (action (transpose 'rows) image) 'values)
          self (dot image image)]
      (transitive
       gram self signed-zero
       (app
        (function/const* 'matrix/gram-action-equivalent-dot-self [])
        'rows 'values 'rows-compatible)
       (app
        (function/const*
         'vector/dot-self-zero-of-equivalent-zero-like [])
        image 'image-zero))))})

(def gram-action-zero-reflects-null-spec
  {:name 'matrix/gram-action-zero-reflects-null :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]
     ['gram-zero
      (seqv
       (dot (action (transpose 'rows) (action 'rows 'values))
            'values)
       signed-zero)]]
    (veq (action 'rows 'values) (vz (action 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]
     ['gram-zero
      (seqv
       (dot (action (transpose 'rows) (action 'rows 'values))
            'values)
       signed-zero)]]
    (let [image (action 'rows 'values)
          gram (dot (action (transpose 'rows) image) 'values)
          self (dot image image)
          gram-self
          (app
           (function/const* 'matrix/gram-action-equivalent-dot-self [])
           'rows 'values 'rows-compatible)
          self-zero
          (transitive self gram signed-zero
                      (symmetric gram self gram-self)
                      'gram-zero)]
      (app (function/const* 'vector/dot-self-zero-reflects [])
           image self-zero)))})

(def gram-action-zero-characterizes-null-spec
  {:name 'matrix/gram-action-zero-characterizes-null :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [image (action 'rows 'values)
          gram (dot (action (transpose 'rows) image) 'values)
          gram-zero (seqv gram signed-zero)
          image-zero (veq image (vz image))]
      (app (function/const* 'proposition/conjunction [])
           (function/arrow gram-zero image-zero)
           (function/arrow image-zero gram-zero))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [image (action 'rows 'values)
          gram (dot (action (transpose 'rows) image) 'values)
          gram-zero (seqv gram signed-zero)
          image-zero (veq image (vz image))]
      (conjp
       (function/arrow gram-zero image-zero)
       (function/arrow image-zero gram-zero)
       (function/lam
        [['zero-proof gram-zero]]
        (app (function/const* 'matrix/gram-action-zero-reflects-null [])
             'rows 'values 'rows-compatible 'zero-proof))
       (function/lam
        [['null-proof image-zero]]
        (app (function/const* 'matrix/gram-action-zero-of-null [])
             'rows 'values 'rows-compatible 'null-proof)))))})

(def definition-specs [])
(def theorem-specs
  [dot-self-zero-of-equivalent-zero-like-spec
   dot-self-zero-reflects-spec
   gram-action-zero-of-null-spec
   gram-action-zero-reflects-null-spec
   gram-action-zero-characterizes-null-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      gram-positive/extend-environment
      (extend-spec-if-missing
       'norm/norm-squared :vector-norm norm/norm-squared-spec)
      (extend-spec-if-missing
       'norm/norm-squared-nonnegative :vector-norm-nonnegative
       norm-positive/norm-squared-nonnegative-spec)
      (extend-spec-if-missing
       'nat/multiply-succ-zero-left :nnrat-add-zero-split
       zero-split/multiply-succ-zero-left-spec)
      (extend-spec-if-missing
       'nnrat/add-cancel-to-zero :nnrat-add-cancel-zero
       add-cancel/add-cancel-to-zero-spec)
      (extend-spec-if-missing
       'nnrat/add-zero-right :nnrat-identities
       identities/add-zero-right-spec)
      (extend-spec-if-missing
       'nnrat/add-zero-left :nnrat-identities
       identities/add-zero-left-spec)
      (extend-spec-if-missing
       'nat/multiply-self-zero :nnrat-quadratic-zero
       quadratic/multiply-self-zero-spec)
      (extend-spec-if-missing
       'nnrat/square-zero-reflects :nnrat-quadratic-zero
       quadratic/square-zero-reflects-spec)
      (extend-spec-if-missing
       'nnrat/quadratic-equality-reflects :nnrat-quadratic-zero
       quadratic/quadratic-equality-reflects-spec)
      (extend-spec-if-missing
       'signed/square-zero-reflects :signed-square-zero
       square-zero/square-zero-reflects-spec)
      add-reflection/extend-environment
      (extend-spec-if-missing
       'signed/equivalent-transitive :signed-map-sum-algebra
       map-sum/equivalent-transitive-spec)
      (extend-spec-if-missing
       'vector/zero-like :vector-additive-units units/zero-like-spec)
      (extend-spec-if-missing
       'vector/equivalent :vector-equivalence
       vector-equivalence/equivalent-spec)
      (extend-spec-if-missing
       'norm/equivalent-zero-like-of-norm-squared-zero
       :vector-norm-zero-reflection
       reflection/equivalent-zero-like-of-norm-squared-zero-spec)
      (support/extend-with :finite-matrix-gram-kernel theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
