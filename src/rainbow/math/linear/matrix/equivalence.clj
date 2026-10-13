(ns rainbow.math.linear.matrix.equivalence
  "Length-sensitive, row-wise equivalence for native finite matrices.

    matrix/equivalent left right

  Matrices are equivalent exactly when they have the same number of rows and
  corresponding rows are vector/equivalent.  Reflexivity and symmetry are
  proved structurally.  Matrix-vector multiplication then respects matrix
  equivalence, and a final theorem composes matrix-side and input-vector
  congruence.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.matrix :as matrix]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.equivalence-laws :as vector-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def truth (function/const* 'proposition/truth []))
(def falsity (function/const* 'proposition/falsity []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def equivalent-spec
  {:name 'matrix/equivalent :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type 'Prop)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      vector-type
      (function/lam
       [['ignored matrix-type]]
       (function/arrow matrix-type 'Prop))
      (function/lam
       [['other matrix-type]]
       (app
        (function/const* 'data/List.rec [type-level type-level])
        vector-type
        (function/lam [['ignored matrix-type]] 'Prop)
        truth
        (function/lam
         [['other-row vector-type] ['other-tail matrix-type]
          ['ignored 'Prop]]
         falsity)
        'other))
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['recur (function/arrow matrix-type 'Prop)]]
       (function/lam
        [['other matrix-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         vector-type
         (function/lam [['ignored matrix-type]] 'Prop)
         falsity
         (function/lam
          [['other-row vector-type] ['other-tail matrix-type]
           ['ignored 'Prop]]
          (conjunction
           (vector-equivalent 'row 'other-row)
           (app 'recur 'other-tail)))
         'other)))
      'left)
     'right))})

(def equivalent-reflexive-spec
  {:name 'matrix/equivalent-reflexive :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent 'rows 'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent 'current 'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-reflexive (app motive 'tail)]]
           (conjoin
            (vector-equivalent 'row 'row)
            (matrix-equivalent 'tail 'tail)
            (app (function/const* 'vector/equivalent-reflexive []) 'row)
            'tail-reflexive))]
      (matrix-rec motive trivial step 'rows)))})

(def equivalent-symmetric-spec
  {:name 'matrix/equivalent-symmetric :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (matrix-equivalent 'right 'left))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (matrix-equivalent 'current-right 'current-left)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (matrix-equivalent 'current-right empty)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]]
                'current-same))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-symmetric (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (matrix-equivalent 'current-right current-left)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                'current-same)
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-proposition
                       (vector-equivalent 'left-row 'right-row)
                       tail-proposition
                       (matrix-equivalent 'left-tail 'right-tail)
                       head-same
                       (proposition-left
                        head-proposition tail-proposition 'current-same)
                       tail-same
                       (proposition-right
                        head-proposition tail-proposition 'current-same)]
                   (conjoin
                    (vector-equivalent 'right-row 'left-row)
                    (matrix-equivalent 'right-tail 'left-tail)
                    (app
                     (function/const* 'vector/equivalent-symmetric [])
                     'left-row 'right-row head-same)
                    (app 'tail-symmetric 'right-tail tail-same)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def vector-multiply-respects-matrix-equivalence-spec
  {:name 'matrix/vector-multiply-respects-matrix-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['same (matrix-equivalent 'left 'right)]]
    (vector-equivalent
     (vector-multiply 'left 'values)
     (vector-multiply 'right 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['same (matrix-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (vector-equivalent
             (vector-multiply 'current-left 'values)
             (vector-multiply 'current-right 'values))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (vector-equivalent
                   (vector-multiply empty 'values)
                   (vector-multiply 'current-right 'values))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (vector-equivalent
                  (vector-multiply empty 'values)
                  (vector-multiply
                   (cons-matrix 'right-row 'right-tail) 'values))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-congruent (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (vector-equivalent
                    (vector-multiply current-left 'values)
                    (vector-multiply 'current-right 'values))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (vector-equivalent
                  (vector-multiply current-left 'values)
                  (vector-multiply (nil-matrix) 'values))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-proposition
                       (vector-equivalent 'left-row 'right-row)
                       tail-proposition
                       (matrix-equivalent 'left-tail 'right-tail)
                       head-same
                       (proposition-left
                        head-proposition tail-proposition 'current-same)
                       tail-same
                       (proposition-right
                        head-proposition tail-proposition 'current-same)]
                   (conjoin
                    (signed-equivalent
                     (dot 'left-row 'values)
                     (dot 'right-row 'values))
                    (vector-equivalent
                     (vector-multiply 'left-tail 'values)
                     (vector-multiply 'right-tail 'values))
                    (app
                     (function/const*
                      'vector/dot-left-respects-equivalence [])
                     'left-row 'right-row 'values head-same)
                    (app 'tail-congruent 'right-tail tail-same)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def vector-multiply-respects-both-equivalences-spec
  {:name 'matrix/vector-multiply-respects-both-equivalences :universes []
   :type
   (function/forall
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-values vector-type] ['right-values vector-type]
     ['rows-same (matrix-equivalent 'left-rows 'right-rows)]
     ['values-same (vector-equivalent 'left-values 'right-values)]]
    (vector-equivalent
     (vector-multiply 'left-rows 'left-values)
     (vector-multiply 'right-rows 'right-values)))
   :value
   (function/lam
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-values vector-type] ['right-values vector-type]
     ['rows-same (matrix-equivalent 'left-rows 'right-rows)]
     ['values-same (vector-equivalent 'left-values 'right-values)]]
    (app
     (function/const* 'vector/equivalent-transitive [])
     (vector-multiply 'left-rows 'left-values)
     (vector-multiply 'right-rows 'left-values)
     (vector-multiply 'right-rows 'right-values)
     (app
      (function/const*
       'matrix/vector-multiply-respects-matrix-equivalence [])
      'left-rows 'right-rows 'left-values 'rows-same)
     (app
      (function/const* 'matrix/vector-multiply-respects-equivalence [])
      'right-rows 'left-values 'right-values 'values-same)))})

(def definition-specs [equivalent-spec])
(def theorem-specs
  [equivalent-reflexive-spec
   equivalent-symmetric-spec
   vector-multiply-respects-matrix-equivalence-spec
   vector-multiply-respects-both-equivalences-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.matrix])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'vector/equivalent-reflexive :vector-equivalence-laws vector-laws/equivalent-reflexive-spec) (extend-spec-if-missing 'vector/equivalent-symmetric :vector-equivalence-laws vector-laws/equivalent-symmetric-spec) (support/extend-with :finite-matrix-equivalence (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.equivalence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
