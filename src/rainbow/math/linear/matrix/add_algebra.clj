(ns rainbow.math.linear.matrix.add-algebra
  "Commutative, associative, quotient-safe native matrix addition.

  Because row-wise matrix/add and vector/add both use symmetric truncating zip
  semantics, commutativity and associativity need no shape premise.  Structural
  congruence in each argument makes the operation well defined over native
  matrix equivalence.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.add-right :as additive]
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
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- absurd [target impossible]
  (app impossible target))

(def add-commutative-spec
  {:name 'matrix/add-commutative :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (matrix-addition 'left 'right)
     (matrix-addition 'right 'left)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (let [motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]]
            (matrix-equivalent
             (matrix-addition 'current-left 'current-right)
             (matrix-addition 'current-right 'current-left))))
          base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (matrix-equivalent
                  (matrix-addition empty 'current-right)
                  (matrix-addition 'current-right empty)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              trivial
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               trivial)
              'current-right)))
          step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-commutative (app motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (matrix-equivalent
                   (matrix-addition current-left 'current-right)
                   (matrix-addition 'current-right current-left)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               trivial
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (conjoin
                 (vector-equivalent
                  (vector-add 'left-row 'right-row)
                  (vector-add 'right-row 'left-row))
                 (matrix-equivalent
                  (matrix-addition 'left-tail 'right-tail)
                  (matrix-addition 'right-tail 'left-tail))
                 (app (function/const* 'vector/add-commutative [])
                      'left-row 'right-row)
                 (app 'tail-commutative 'right-tail)))
               'current-right))))]
      (app (matrix-rec motive base step 'left) 'right)))})

(def add-associative-spec
  {:name 'matrix/add-associative :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (matrix-addition (matrix-addition 'left 'middle) 'right)
     (matrix-addition
      'left (matrix-addition 'middle 'right))))
   :value
   (function/lam
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-middle matrix-type] ['current-right matrix-type]]
            (matrix-equivalent
             (matrix-addition
              (matrix-addition 'current-left 'current-middle)
              'current-right)
             (matrix-addition
              'current-left
              (matrix-addition 'current-middle 'current-right)))))
          outer-base
          (function/lam
           [['current-middle matrix-type] ['current-right matrix-type]]
           trivial)
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-associative (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle matrix-type]]
                  (function/forall
                   [['current-right matrix-type]]
                   (matrix-equivalent
                    (matrix-addition
                     (matrix-addition current-left 'current-middle)
                     'current-right)
                    (matrix-addition
                     current-left
                     (matrix-addition
                      'current-middle 'current-right)))))]
             (function/lam
              [['current-middle matrix-type]]
              (matrix-rec
               middle-motive
               (function/lam
                [['current-right matrix-type]]
                trivial)
               (function/lam
                [['middle-row vector-type] ['middle-tail matrix-type]
                 ['ignored-middle (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-matrix 'middle-row 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right matrix-type]]
                       (matrix-equivalent
                        (matrix-addition
                         (matrix-addition current-left current-middle)
                         'current-right)
                        (matrix-addition
                         current-left
                         (matrix-addition
                          current-middle 'current-right))))]
                  (function/lam
                   [['current-right matrix-type]]
                   (matrix-rec
                    right-motive
                    trivial
                    (function/lam
                     [['right-row vector-type] ['right-tail matrix-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (conjoin
                      (vector-equivalent
                       (vector-add
                        (vector-add 'left-row 'middle-row)
                        'right-row)
                       (vector-add
                        'left-row
                        (vector-add 'middle-row 'right-row)))
                      (matrix-equivalent
                       (matrix-addition
                        (matrix-addition 'left-tail 'middle-tail)
                        'right-tail)
                       (matrix-addition
                        'left-tail
                        (matrix-addition
                         'middle-tail 'right-tail)))
                      (app (function/const* 'vector/add-associative [])
                           'left-row 'middle-row 'right-row)
                      (app 'tail-associative
                           'middle-tail 'right-tail)))
                    'current-right))))
               'current-middle))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'middle 'right)))})

(def add-respects-left-equivalence-spec
  {:name 'matrix/add-respects-left-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type]
     ['same (matrix-equivalent 'left 'equivalent-left)]]
    (matrix-equivalent
     (matrix-addition 'left 'right)
     (matrix-addition 'equivalent-left 'right)))
   :value
   (function/lam
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type]
     ['same (matrix-equivalent 'left 'equivalent-left)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-equivalent-left matrix-type]
             ['current-right matrix-type]
             ['current-same
              (matrix-equivalent
               'current-left 'current-equivalent-left)]]
            (matrix-equivalent
             (matrix-addition 'current-left 'current-right)
             (matrix-addition
              'current-equivalent-left 'current-right))))
          outer-base
          (let [empty (nil-matrix)
                equivalent-motive
                (function/lam
                 [['current-equivalent-left matrix-type]]
                 (function/forall
                  [['current-right matrix-type]
                   ['current-same
                    (matrix-equivalent
                     empty 'current-equivalent-left)]]
                  (matrix-equivalent
                   (matrix-addition empty 'current-right)
                   (matrix-addition
                    'current-equivalent-left 'current-right))))]
            (function/lam
             [['current-equivalent-left matrix-type]]
             (matrix-rec
              equivalent-motive
              (function/lam
               [['current-right matrix-type]
                ['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['other-row vector-type] ['other-tail matrix-type]
                ['ignored (app equivalent-motive 'other-tail)]]
               (function/lam
                [['current-right matrix-type]
                 ['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'other-row 'other-tail))]]
                (absurd
                 (matrix-equivalent
                  (matrix-addition empty 'current-right)
                  (matrix-addition
                   (cons-matrix 'other-row 'other-tail)
                   'current-right))
                 'current-same)))
              'current-equivalent-left)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-respects (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 equivalent-motive
                 (function/lam
                  [['current-equivalent-left matrix-type]]
                  (function/forall
                   [['current-right matrix-type]
                    ['current-same
                     (matrix-equivalent
                      current-left 'current-equivalent-left)]]
                   (matrix-equivalent
                    (matrix-addition current-left 'current-right)
                    (matrix-addition
                     'current-equivalent-left 'current-right))))]
             (function/lam
              [['current-equivalent-left matrix-type]]
              (matrix-rec
               equivalent-motive
               (function/lam
                [['current-right matrix-type]
                 ['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (matrix-addition current-left 'current-right)
                  (matrix-addition (nil-matrix) 'current-right))
                 'current-same))
               (function/lam
                [['other-row vector-type] ['other-tail matrix-type]
                 ['ignored (app equivalent-motive 'other-tail)]]
                (function/lam
                 [['current-right matrix-type]
                  ['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'other-row 'other-tail))]]
                 (let [head-same
                       (vector-equivalent 'left-row 'other-row)
                       tail-same
                       (matrix-equivalent 'left-tail 'other-tail)
                       current-head-same
                       (proposition-left
                        head-same tail-same 'current-same)
                       current-tail-same
                       (proposition-right
                        head-same tail-same 'current-same)
                       right-motive
                       (function/lam
                        [['current-offset matrix-type]]
                        (matrix-equivalent
                         (matrix-addition current-left 'current-offset)
                         (matrix-addition
                          (cons-matrix 'other-row 'other-tail)
                          'current-offset)))]
                   (matrix-rec
                    right-motive
                    trivial
                    (function/lam
                     [['right-row vector-type] ['right-tail matrix-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (conjoin
                      (vector-equivalent
                       (vector-add 'left-row 'right-row)
                       (vector-add 'other-row 'right-row))
                      (matrix-equivalent
                       (matrix-addition 'left-tail 'right-tail)
                       (matrix-addition 'other-tail 'right-tail))
                      (app
                       (function/const*
                        'vector/add-respects-equivalence [])
                       'left-row 'other-row 'right-row 'right-row
                       current-head-same
                       (app
                        (function/const* 'vector/equivalent-reflexive [])
                        'right-row))
                      (app 'tail-respects
                           'other-tail 'right-tail current-tail-same)))
                    'current-right))))
               'current-equivalent-left))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'equivalent-left 'right 'same)))})

(def add-respects-right-equivalence-spec
  {:name 'matrix/add-respects-right-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['equivalent-right matrix-type]
     ['same (matrix-equivalent 'right 'equivalent-right)]]
    (matrix-equivalent
     (matrix-addition 'left 'right)
     (matrix-addition 'left 'equivalent-right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['equivalent-right matrix-type]
     ['same (matrix-equivalent 'right 'equivalent-right)]]
    (let [start (matrix-addition 'left 'right)
          commuted (matrix-addition 'right 'left)
          replaced (matrix-addition 'equivalent-right 'left)
          finish (matrix-addition 'left 'equivalent-right)]
      (transitive
       start replaced finish
       (transitive
        start commuted replaced
        (app (function/const* 'matrix/add-commutative [])
             'left 'right)
        (app
         (function/const* 'matrix/add-respects-left-equivalence [])
         'right 'equivalent-right 'left 'same))
       (app (function/const* 'matrix/add-commutative [])
            'equivalent-right 'left))))})

(def add-respects-equivalence-spec
  {:name 'matrix/add-respects-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]]
    (matrix-equivalent
     (matrix-addition 'left 'right)
     (matrix-addition 'equivalent-left 'equivalent-right)))
   :value
   (function/lam
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]]
    (transitive
     (matrix-addition 'left 'right)
     (matrix-addition 'equivalent-left 'right)
     (matrix-addition 'equivalent-left 'equivalent-right)
     (app
      (function/const* 'matrix/add-respects-left-equivalence [])
      'left 'equivalent-left 'right 'left-same)
     (app
      (function/const* 'matrix/add-respects-right-equivalence [])
      'equivalent-left 'right 'equivalent-right 'right-same)))})

(def definition-specs [])
(def theorem-specs
  [add-commutative-spec
   add-associative-spec
   add-respects-left-equivalence-spec
   add-respects-right-equivalence-spec
   add-respects-equivalence-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      additive/extend-environment
      (support/extend-with :finite-matrix-add-algebra theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
