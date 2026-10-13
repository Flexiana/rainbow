(ns rainbow.math.linear.matrix.row-gram-kernel
  "Zero-kernel characterization for the native row Gram product AA^T.

  Under the exact rectangular positive-width and compatibility premises used by
  the row-Gram identity, x^T AA^T x is zero exactly when A^T x is componentwise
  equivalent to its shape-preserving zero vector.  Both implications and their
  conjunction are ordinary theorem data, kernel-checked and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.row-gram :as row-gram]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- cv [h q] (app (function/const* 'data/cons [t]) signed h q))
(defn- cm [h q] (app (function/const* 'data/cons [t]) vector-type h q))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- vz [values] (app (function/const* 'vector/zero-like []) values))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
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

(def row-gram-action-zero-of-transpose-null-spec
  {:name 'matrix/row-gram-action-zero-of-transpose-null :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]
     ['transpose-image-zero
      (let [rows (cm (cv 'head 'row-tail) 'tail)
            image (action (transpose rows) 'values)]
        (veq image (vz image)))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)]
      (seqv (dot (action rows image) 'values) signed-zero)))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]
     ['transpose-image-zero
      (let [rows (cm (cv 'head 'row-tail) 'tail)
            image (action (transpose rows) 'values)]
        (veq image (vz image)))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)
          quadratic (dot (action rows image) 'values)
          self (dot image image)]
      (transitive
       quadratic self signed-zero
       (app
        (function/const*
         'matrix/row-gram-action-equivalent-dot-self [])
        'head 'row-tail 'tail 'values
        'rows-rectangular 'transpose-compatible)
       (app
        (function/const*
         'vector/dot-self-zero-of-equivalent-zero-like [])
        image 'transpose-image-zero))))})

(def row-gram-action-zero-reflects-transpose-null-spec
  {:name 'matrix/row-gram-action-zero-reflects-transpose-null :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]
     ['quadratic-zero
      (let [rows (cm (cv 'head 'row-tail) 'tail)
            image (action (transpose rows) 'values)]
        (seqv (dot (action rows image) 'values) signed-zero))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)]
      (veq image (vz image))))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]
     ['quadratic-zero
      (let [rows (cm (cv 'head 'row-tail) 'tail)
            image (action (transpose rows) 'values)]
        (seqv (dot (action rows image) 'values) signed-zero))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)
          quadratic (dot (action rows image) 'values)
          self (dot image image)
          quadratic-self
          (app
           (function/const*
            'matrix/row-gram-action-equivalent-dot-self [])
           'head 'row-tail 'tail 'values
           'rows-rectangular 'transpose-compatible)
          self-zero
          (transitive self quadratic signed-zero
                      (symmetric quadratic self quadratic-self)
                      'quadratic-zero)]
      (app (function/const* 'vector/dot-self-zero-reflects [])
           image self-zero)))})

(def row-gram-action-zero-characterizes-transpose-null-spec
  {:name 'matrix/row-gram-action-zero-characterizes-transpose-null :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)
          quadratic-zero
          (seqv (dot (action rows image) 'values) signed-zero)
          image-zero (veq image (vz image))]
      (app (function/const* 'proposition/conjunction [])
           (function/arrow quadratic-zero image-zero)
           (function/arrow image-zero quadratic-zero))))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['values vector-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]
     ['transpose-compatible
      (compatible
       (transpose (cm (cv 'head 'row-tail) 'tail)) 'values)]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          image (action (transpose rows) 'values)
          quadratic-zero
          (seqv (dot (action rows image) 'values) signed-zero)
          image-zero (veq image (vz image))]
      (conjp
       (function/arrow quadratic-zero image-zero)
       (function/arrow image-zero quadratic-zero)
       (function/lam
        [['zero-proof quadratic-zero]]
        (app
         (function/const*
          'matrix/row-gram-action-zero-reflects-transpose-null [])
         'head 'row-tail 'tail 'values
         'rows-rectangular 'transpose-compatible 'zero-proof))
       (function/lam
        [['null-proof image-zero]]
        (app
         (function/const*
          'matrix/row-gram-action-zero-of-transpose-null [])
         'head 'row-tail 'tail 'values
         'rows-rectangular 'transpose-compatible 'null-proof)))))})

(def definition-specs [])
(def theorem-specs
  [row-gram-action-zero-of-transpose-null-spec
   row-gram-action-zero-reflects-transpose-null-spec
   row-gram-action-zero-characterizes-transpose-null-spec])

(defn extend-environment [env]
  (-> env
      row-gram/extend-environment
      (support/extend-with :finite-matrix-row-gram-kernel theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
