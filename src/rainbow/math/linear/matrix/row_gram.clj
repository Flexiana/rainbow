(ns rainbow.math.linear.matrix.row-gram
  "Symmetry and positive semidefiniteness of the native row Gram product.

  For a rectangular matrix A with an explicitly nonempty first row, total
  transpose is involutive.  Consequently AA^T is symmetric, and its quadratic
  action is equivalent to the self-dot of A^T x.  The latter is nonnegative for
  arbitrary signed entries.  The positive-width premise is mathematically exact
  for Rainbow's row-list encoding, which forgets nonempty zero-width matrices
  under transpose.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.gram-kernel :as gram-kernel]
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
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- meq [a b] (app (function/const* 'matrix/equivalent []) a b))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [a b]
  (app (function/const* 'matrix/multiply []) a b))
(defn- strans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- ssym [a b same]
  (app (function/const* 'signed/equivalent-symmetric []) a b same))
(defn- msym [a b same]
  (app (function/const* 'matrix/equivalent-symmetric []) a b same))
(defn- mtrans [a b c ab bc]
  (app (function/const* 'matrix/equivalent-transitive []) a b c ab bc))

(def row-gram-symmetric-spec
  {:name 'matrix/row-gram-symmetric-positive-width :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          product (multiply rows (transpose rows))]
      (meq (transpose product) product)))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cm (cv 'head 'row-tail) 'tail))]]
    (let [rows (cm (cv 'head 'row-tail) 'tail)
          rows-transpose (transpose rows)
          twice (transpose rows-transpose)
          product (multiply rows rows-transpose)
          reversed (multiply twice rows-transpose)
          involutive
          (app
           (function/const*
            'matrix/transpose-involutive-nonempty-width [])
           'head 'row-tail 'tail 'rows-rectangular)]
      (mtrans
       (transpose product) reversed product
       (app
        (function/const*
         'matrix/transpose-multiply-reverses-positive-width [])
        'head 'row-tail 'tail rows-transpose 'rows-rectangular)
       (app
        (function/const* 'matrix/multiply-respects-left-equivalence [])
        twice rows rows-transpose involutive))))})

(def row-gram-action-dot-self-spec
  {:name 'matrix/row-gram-action-equivalent-dot-self :universes []
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
          image (action (transpose rows) 'values)]
      (seqv
       (dot (action rows image) 'values)
       (dot image image))))
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
          rows-transpose (transpose rows)
          twice (transpose rows-transpose)
          image (action rows-transpose 'values)
          start (dot (action rows image) 'values)
          middle (dot (action twice image) 'values)
          finish (dot image image)
          involutive
          (app
           (function/const*
            'matrix/transpose-involutive-nonempty-width [])
           'head 'row-tail 'tail 'rows-rectangular)
          rows-twice
          (msym twice rows involutive)
          actions-same
          (app
           (function/const*
            'matrix/vector-multiply-respects-matrix-equivalence [])
           rows twice image rows-twice)]
      (strans
       start middle finish
       (app (function/const* 'vector/dot-left-respects-equivalence [])
            (action rows image) (action twice image)
            'values actions-same)
       (app
        (function/const* 'matrix/gram-action-equivalent-dot-self [])
        rows-transpose 'values 'transpose-compatible))))})

(def row-gram-action-nonnegative-spec
  {:name 'matrix/row-gram-action-nonnegative :universes []
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
          image (action (transpose rows) 'values)]
      (sle signed-zero (dot (action rows image) 'values))))
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
          quadratic (dot (action rows image) 'values)
          self (dot image image)
          quadratic-self
          (app
           (function/const*
            'matrix/row-gram-action-equivalent-dot-self [])
           'head 'row-tail 'tail 'values
           'rows-rectangular 'transpose-compatible)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       signed-zero signed-zero self quadratic
       (app (function/const* 'signed/equivalent-reflexive [])
            signed-zero)
       (ssym quadratic self quadratic-self)
       (app (function/const* 'vector/dot-self-nonnegative []) image))))})

(def definition-specs [])
(def theorem-specs
  [row-gram-symmetric-spec
   row-gram-action-dot-self-spec
   row-gram-action-nonnegative-spec])

(defn extend-environment [env]
  (-> env
      gram-kernel/extend-environment
      (support/extend-with :finite-matrix-row-gram theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
