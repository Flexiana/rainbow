(ns rainbow.math.linear.matrix.row-length-shape
  "Bridges executable row-length evidence to abstract matrix shape certificates.

  Matrix algorithms use `vector/same-shape`, `matrix/compatible`, and
  `matrix/rectangular` because those propositions compose well in proofs.  A
  parser or certificate checker, however, observes natural-number lengths.
  This module closes that boundary:

    equal vector lengths                 -> vector/same-shape
    every row has the reference length  -> matrix/compatible
    every row has the reference length  -> matrix/rectangular

  The empty/nonempty mismatch cases are eliminated with Nat no-confusion, not
  assumed.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.composable :as composable]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.linear.vector.shape-cancellation :as vector-shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def zero-nat (function/const* 'data/zero []))
(def signed-zero (function/const* 'signed/zero []))
(def truth (function/const* 'proposition/truth []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- vector-rec-data [motive base step values]
  (app (function/const* 'data/List.rec [type-level type-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- matrix-rec-family [motive base step rows]
  (app (function/const* 'data/List.rec [type-level type-level])
       vector-type motive base step rows))
(defn- length-of [values]
  (app (function/const* 'vector/length []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- row-length-compatible [rows values]
  (app (function/const* 'matrix/row-length-compatible []) rows values))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- symmetric-nat [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       nat left right same))
(defn- reflexive-nat [value]
  (app (function/const* 'equality/reflexive [type-level]) nat value))
(defn- successor-congruent [left right same]
  (app (function/const* 'equality/congruent-function
                        [type-level type-level])
       nat nat (function/const* 'data/succ []) left right same))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- left-proof [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-proof [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- explode [goal impossible]
  (app (function/const* 'proposition/explode []) goal impossible))

(def length-spec
  {:name 'vector/length :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type nat)
   :value
   (function/lam
    [['values vector-type]]
    (vector-rec-data
     (function/lam [['ignored vector-type]] nat)
     zero-nat
     (function/lam
      [['head signed] ['tail vector-type] ['tail-length nat]]
      (succ 'tail-length))
     'values))})

(def row-length-compatible-spec
  {:name 'matrix/row-length-compatible :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type 'Prop)
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (app
     (matrix-rec-family
      (function/lam
       [['ignored matrix-type]]
       (function/arrow vector-type 'Prop))
      (function/lam [['ignored-values vector-type]] truth)
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['tail-certificate (function/arrow vector-type 'Prop)]]
       (function/lam
        [['current-values vector-type]]
        (conjunction
         (nat-equality (length-of 'row) (length-of 'current-values))
         (app 'tail-certificate 'current-values))))
      'rows)
     'values))})

(def length-equality-implies-same-shape-spec
  {:name 'vector/length-equality-implies-same-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same-length (nat-equality (length-of 'left) (length-of 'right))]]
    (same-shape 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same-length (nat-equality (length-of 'left) (length-of 'right))]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same-length
              (nat-equality (length-of 'current-left)
                            (length-of 'current-right))]]
            (same-shape 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/arrow
                  (nat-equality (length-of empty) (length-of 'current-right))
                  (same-shape empty 'current-right)))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              inner-motive
              (function/lam
               [['current-same-length
                 (nat-equality (length-of empty) (length-of empty))]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app inner-motive 'right-tail)]]
               (function/lam
                [['current-same-length
                  (nat-equality
                   (length-of empty)
                   (length-of (cons-vector 'right-head 'right-tail)))]]
                (explode
                 (same-shape empty (cons-vector 'right-head 'right-tail))
                 (app (function/const* 'nat/zero-not-successor [])
                      (length-of 'right-tail) 'current-same-length))))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-law (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/arrow
                   (nat-equality (length-of current-left)
                                 (length-of 'current-right))
                   (same-shape current-left 'current-right)))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               inner-motive
               (function/lam
                [['current-same-length
                  (nat-equality (length-of current-left)
                                (length-of (nil-vector)))]]
                (explode
                 (same-shape current-left (nil-vector))
                 (app
                  (function/const* 'nat/zero-not-successor [])
                  (length-of 'left-tail)
                  (symmetric-nat
                   (length-of current-left) (length-of (nil-vector))
                   'current-same-length))))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app inner-motive 'right-tail)]]
                (function/lam
                 [['current-same-length
                   (nat-equality
                    (length-of current-left)
                    (length-of (cons-vector 'right-head 'right-tail)))]]
                 (let [tail-same-length
                       (app (function/const* 'nat/successor-injective [])
                            (length-of 'left-tail) (length-of 'right-tail)
                            'current-same-length)
                       tail-shape
                       (app 'tail-law 'right-tail tail-same-length)]
                   (conjoin
                    (app (function/const* 'signed/equivalent [])
                         signed-zero signed-zero)
                    (same-shape 'left-tail 'right-tail)
                    (app (function/const* 'signed/equivalent-reflexive [])
                         signed-zero)
                    tail-shape))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'same-length)))})

(def row-length-compatible-implies-compatible-spec
  {:name 'matrix/row-length-compatible-implies-compatible :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['length-certificate (row-length-compatible 'rows 'values)]]
    (compatible 'rows 'values))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['length-certificate (row-length-compatible 'rows 'values)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-values vector-type]
             ['current-length-certificate
              (row-length-compatible 'current-rows 'current-values)]]
            (compatible 'current-rows 'current-values)))
          base
          (function/lam
           [['current-values vector-type]
            ['current-length-certificate
             (row-length-compatible (nil-matrix) 'current-values)]]
           trivial)
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-values vector-type]
             ['current-length-certificate
              (row-length-compatible
               (cons-matrix 'row 'tail) 'current-values)]]
            (let [row-length-equality
                  (left-proof
                   (nat-equality (length-of 'row)
                                 (length-of 'current-values))
                   (row-length-compatible 'tail 'current-values)
                   'current-length-certificate)
                  tail-length-certificate
                  (right-proof
                   (nat-equality (length-of 'row)
                                 (length-of 'current-values))
                   (row-length-compatible 'tail 'current-values)
                   'current-length-certificate)]
              (conjoin
               (same-shape 'row 'current-values)
               (compatible 'tail 'current-values)
               (app
                (function/const*
                 'vector/length-equality-implies-same-shape [])
                'row 'current-values row-length-equality)
               (app 'tail-law 'current-values tail-length-certificate)))))]
      (app (matrix-rec motive base step 'rows)
           'values 'length-certificate)))})

(def same-shape-implies-length-equality-spec
  {:name 'vector/same-shape-implies-length-equality :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (nat-equality (length-of 'left) (length-of 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same (same-shape 'current-left 'current-right)]]
            (nat-equality (length-of 'current-left)
                          (length-of 'current-right))))
          outer-base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/arrow
                  (same-shape empty 'current-right)
                  (nat-equality (length-of empty)
                                (length-of 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              inner-motive
              (function/lam
               [['current-same (same-shape empty empty)]]
               (reflexive-nat zero-nat))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app inner-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (same-shape
                   empty (cons-vector 'right-head 'right-tail))]]
                (explode
                 (nat-equality
                  (length-of empty)
                  (length-of (cons-vector 'right-head 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-law (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/arrow
                   (same-shape current-left 'current-right)
                   (nat-equality (length-of current-left)
                                 (length-of 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               inner-motive
               (function/lam
                [['current-same
                  (same-shape current-left (nil-vector))]]
                (explode
                 (nat-equality (length-of current-left)
                               (length-of (nil-vector)))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app inner-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (same-shape
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [tail-shape
                       (right-proof
                        (app (function/const* 'signed/equivalent [])
                             signed-zero signed-zero)
                        (same-shape 'left-tail 'right-tail)
                        'current-same)
                       tail-length
                       (app 'tail-law 'right-tail tail-shape)]
                   (successor-congruent
                    (length-of 'left-tail) (length-of 'right-tail)
                    tail-length))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def compatible-implies-row-length-compatible-spec
  {:name 'matrix/compatible-implies-row-length-compatible :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['shape-certificate (compatible 'rows 'values)]]
    (row-length-compatible 'rows 'values))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['shape-certificate (compatible 'rows 'values)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-values vector-type]
             ['current-shape-certificate
              (compatible 'current-rows 'current-values)]]
            (row-length-compatible 'current-rows 'current-values)))
          base
          (function/lam
           [['current-values vector-type]
            ['current-shape-certificate
             (compatible (nil-matrix) 'current-values)]]
           trivial)
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-values vector-type]
             ['current-shape-certificate
              (compatible (cons-matrix 'row 'tail) 'current-values)]]
            (let [row-shape
                  (left-proof
                   (same-shape 'row 'current-values)
                   (compatible 'tail 'current-values)
                   'current-shape-certificate)
                  tail-shape
                  (right-proof
                   (same-shape 'row 'current-values)
                   (compatible 'tail 'current-values)
                   'current-shape-certificate)]
              (conjoin
               (nat-equality (length-of 'row)
                             (length-of 'current-values))
               (row-length-compatible 'tail 'current-values)
               (app
                (function/const*
                 'vector/same-shape-implies-length-equality [])
                'row 'current-values row-shape)
               (app 'tail-law 'current-values tail-shape)))))]
      (app (matrix-rec motive base step 'rows)
           'values 'shape-certificate)))})

(def row-length-compatible-implies-rectangular-spec
  {:name 'matrix/row-length-compatible-implies-rectangular :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['length-certificate (row-length-compatible 'rows 'values)]]
    (rectangular 'rows))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['length-certificate (row-length-compatible 'rows 'values)]]
    (app
     (function/const* 'matrix/compatible-implies-rectangular [])
     'rows 'values
     (app
      (function/const*
       'matrix/row-length-compatible-implies-compatible [])
      'rows 'values 'length-certificate)))})

(def rectangular-implies-head-row-length-compatible-spec
  {:name 'matrix/rectangular-implies-head-row-length-compatible :universes []
   :type
   (function/forall
    [['head vector-type] ['tail matrix-type]
     ['shape-certificate (rectangular (cons-matrix 'head 'tail))]]
    (row-length-compatible (cons-matrix 'head 'tail) 'head))
   :value
   (function/lam
    [['head vector-type] ['tail matrix-type]
     ['shape-certificate (rectangular (cons-matrix 'head 'tail))]]
    (app
     (function/const*
      'matrix/compatible-implies-row-length-compatible [])
     (cons-matrix 'head 'tail) 'head
     (app
      (function/const*
       'matrix/compatible-with-head-of-rectangular [])
      'head 'tail 'shape-certificate)))})

(def definition-specs [length-spec row-length-compatible-spec])
(def theorem-specs
  [length-equality-implies-same-shape-spec
   same-shape-implies-length-equality-spec
   row-length-compatible-implies-compatible-spec
   compatible-implies-row-length-compatible-spec
   row-length-compatible-implies-rectangular-spec
   rectangular-implies-head-row-length-compatible-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.composable])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'nat/predecessor :nat-infinite nat-infinite/predecessor-spec) (extend-spec-if-missing 'nat/zero-not-successor :nat-infinite nat-infinite/zero-not-successor-spec) (extend-spec-if-missing 'nat/successor-injective :nat-infinite nat-infinite/successor-injective-spec) (extend-spec-if-missing 'vector/same-shape-reflexive :vector-shape-cancellation vector-shape/same-shape-reflexive-spec) (extend-spec-if-missing 'matrix/compatible-with-head-of-rectangular :finite-matrix-shape matrix-shape/compatible-with-head-of-rectangular-spec) (support/extend-with :finite-matrix-row-length-shape (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.row-length-shape))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
