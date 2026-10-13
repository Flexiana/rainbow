(ns rainbow.math.linear.matrix.additive-group
  "Shaped zero, negation, subtraction, and inverse laws for matrices.

  The three operations map existing vector operations over rows (with
  subtraction defined by addition and negation).  Zero and negation preserve
  complete matrix shape; same-shaped subtraction preserves both operand shapes.
  Matrix addition has shaped identities and inverses, including self-subtraction
  to the shaped zero matrix.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.add-algebra :as algebra]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- list-map [mapping rows]
  (app (function/const* 'list/map [type-level type-level])
       vector-type vector-type mapping rows))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-zero-like [rows]
  (app (function/const* 'matrix/zero-like []) rows))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- matrix-subtract [left right]
  (app (function/const* 'matrix/subtract []) left right))
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'matrix/same-shape-transitive [])
       left middle right first second))

(def zero-like-spec
  {:name 'matrix/zero-like :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type)
   :value
   (function/lam
    [['rows matrix-type]]
    (list-map
     (function/lam
      [['row vector-type]]
      (vector-zero-like 'row))
     'rows))})

(def negate-spec
  {:name 'matrix/negate :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type)
   :value
   (function/lam
    [['rows matrix-type]]
    (list-map
     (function/lam
      [['row vector-type]]
      (vector-negate 'row))
     'rows))})

(def subtract-spec
  {:name 'matrix/subtract :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type matrix-type)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (matrix-addition 'left (matrix-negate 'right)))})

(def zero-like-preserves-same-shape-spec
  {:name 'matrix/zero-like-preserves-same-shape :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-same-shape (matrix-zero-like 'rows) 'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-same-shape (matrix-zero-like 'current) 'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (vector-same-shape (vector-zero-like 'row) 'row)
            (matrix-same-shape (matrix-zero-like 'tail) 'tail)
            (app (function/const* 'vector/zero-like-preserves-shape [])
                 'row)
            'tail-shape))]
      (matrix-rec motive trivial step 'rows)))})

(def negate-preserves-same-shape-spec
  {:name 'matrix/negate-preserves-same-shape :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-same-shape (matrix-negate 'rows) 'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-same-shape (matrix-negate 'current) 'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (vector-same-shape (vector-negate 'row) 'row)
            (matrix-same-shape (matrix-negate 'tail) 'tail)
            (app (function/const* 'vector/negate-preserves-shape [])
                 'row)
            'tail-shape))]
      (matrix-rec motive trivial step 'rows)))})

(def subtract-preserves-shape-spec
  {:name 'matrix/subtract-preserves-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (conjunction
     (matrix-same-shape (matrix-subtract 'left 'right) 'left)
     (matrix-same-shape (matrix-subtract 'left 'right) 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (let [negated (matrix-negate 'right)
          negated-right
          (app (function/const* 'matrix/negate-preserves-same-shape [])
               'right)
          right-negated
          (app (function/const* 'matrix/same-shape-symmetric [])
               negated 'right negated-right)
          left-negated
          (shape-transitive
           'left 'right negated 'same right-negated)
          sum-left
          (matrix-same-shape
           (matrix-addition 'left negated) 'left)
          sum-negated
          (matrix-same-shape
           (matrix-addition 'left negated) negated)
          sum-both
          (app (function/const* 'matrix/add-preserves-shape [])
               'left negated left-negated)
          sum-left-proof
          (proposition-left sum-left sum-negated sum-both)
          sum-negated-proof
          (proposition-right sum-left sum-negated sum-both)]
      (conjoin
       sum-left
       (matrix-same-shape
        (matrix-subtract 'left 'right) 'right)
       sum-left-proof
       (shape-transitive
        (matrix-subtract 'left 'right) negated 'right
        sum-negated-proof negated-right))))})

(def add-zero-like-right-spec
  {:name 'matrix/add-zero-like-right :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-addition 'rows (matrix-zero-like 'rows))
     'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-addition 'current (matrix-zero-like 'current))
            'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-identity (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-add 'row (vector-zero-like 'row)) 'row)
            (matrix-equivalent
             (matrix-addition 'tail (matrix-zero-like 'tail))
             'tail)
            (app (function/const* 'vector/add-zero-like-right []) 'row)
            'tail-identity))]
      (matrix-rec motive trivial step 'rows)))})

(def add-zero-like-left-spec
  {:name 'matrix/add-zero-like-left :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-addition (matrix-zero-like 'rows) 'rows)
     'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (equivalent-transitive
     (matrix-addition (matrix-zero-like 'rows) 'rows)
     (matrix-addition 'rows (matrix-zero-like 'rows))
     'rows
     (app (function/const* 'matrix/add-commutative [])
          (matrix-zero-like 'rows) 'rows)
     (app (function/const* 'matrix/add-zero-like-right []) 'rows)))})

(def add-negate-right-spec
  {:name 'matrix/add-negate-right-equivalent-zero-like :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-addition 'rows (matrix-negate 'rows))
     (matrix-zero-like 'rows)))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-addition 'current (matrix-negate 'current))
            (matrix-zero-like 'current)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-inverse (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-add 'row (vector-negate 'row))
             (vector-zero-like 'row))
            (matrix-equivalent
             (matrix-addition 'tail (matrix-negate 'tail))
             (matrix-zero-like 'tail))
            (app
             (function/const*
              'vector/add-negate-right-equivalent-zero-like [])
             'row)
            'tail-inverse))]
      (matrix-rec motive trivial step 'rows)))})

(def add-negate-left-spec
  {:name 'matrix/add-negate-left-equivalent-zero-like :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-addition (matrix-negate 'rows) 'rows)
     (matrix-zero-like 'rows)))
   :value
   (function/lam
    [['rows matrix-type]]
    (equivalent-transitive
     (matrix-addition (matrix-negate 'rows) 'rows)
     (matrix-addition 'rows (matrix-negate 'rows))
     (matrix-zero-like 'rows)
     (app (function/const* 'matrix/add-commutative [])
          (matrix-negate 'rows) 'rows)
     (app
      (function/const*
       'matrix/add-negate-right-equivalent-zero-like [])
      'rows)))})

(def subtract-self-spec
  {:name 'matrix/subtract-self-equivalent-zero-like :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-subtract 'rows 'rows)
     (matrix-zero-like 'rows)))
   :value
   (function/lam
    [['rows matrix-type]]
    (app
     (function/const*
      'matrix/add-negate-right-equivalent-zero-like [])
     'rows))})

(def definition-specs [zero-like-spec negate-spec subtract-spec])
(def theorem-specs
  [zero-like-preserves-same-shape-spec
   negate-preserves-same-shape-spec
   subtract-preserves-shape-spec
   add-zero-like-right-spec
   add-zero-like-left-spec
   add-negate-right-spec
   add-negate-left-spec
   subtract-self-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.add-algebra])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-additive-group (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.additive-group))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
