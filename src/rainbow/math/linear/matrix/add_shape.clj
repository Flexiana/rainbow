(ns rainbow.math.linear.matrix.add-shape
  "Equivalence laws for matrix shape and shape preservation by addition.

  The structural matrix/same-shape relation is symmetric and transitive.
  Adding same-shaped matrices preserves the complete two-level shape of both
  inputs.  These certificates are the shape infrastructure needed to transport
  addition through total transpose.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.add :as matrix-add]
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
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
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

(def same-shape-symmetric-spec
  {:name 'matrix/same-shape-symmetric :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (matrix-same-shape 'right 'left))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-same-shape 'current-left 'current-right)]]
            (matrix-same-shape 'current-right 'current-left)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-same-shape empty 'current-right)]]
                  (matrix-same-shape 'current-right empty)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-same-shape empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-same-shape
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (matrix-same-shape
                  (cons-matrix 'right-row 'right-tail) empty)
                 'current-same)))
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
                     (matrix-same-shape current-left 'current-right)]]
                   (matrix-same-shape 'current-right current-left)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (matrix-same-shape (nil-matrix) current-left)
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-same-shape
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-shape
                       (vector-same-shape 'left-row 'right-row)
                       tail-shape
                       (matrix-same-shape 'left-tail 'right-tail)]
                   (conjoin
                    (vector-same-shape 'right-row 'left-row)
                    (matrix-same-shape 'right-tail 'left-tail)
                    (app
                     (function/const* 'vector/same-shape-symmetric [])
                     'left-row 'right-row
                     (proposition-left
                      head-shape tail-shape 'current-same))
                    (app 'tail-symmetric 'right-tail
                         (proposition-right
                          head-shape tail-shape 'current-same))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def same-shape-transitive-spec
  {:name 'matrix/same-shape-transitive :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-same-shape 'left 'middle)]
     ['middle-right (matrix-same-shape 'middle 'right)]]
    (matrix-same-shape 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-same-shape 'left 'middle)]
     ['middle-right (matrix-same-shape 'middle 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-middle matrix-type] ['current-right matrix-type]
             ['current-left-middle
              (matrix-same-shape 'current-left 'current-middle)]
             ['current-middle-right
              (matrix-same-shape 'current-middle 'current-right)]]
            (matrix-same-shape 'current-left 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                middle-motive
                (function/lam
                 [['current-middle matrix-type]]
                 (function/forall
                  [['current-right matrix-type]
                   ['current-left-middle
                    (matrix-same-shape empty 'current-middle)]
                   ['current-middle-right
                    (matrix-same-shape 'current-middle 'current-right)]]
                  (matrix-same-shape empty 'current-right)))]
            (function/lam
             [['current-middle matrix-type]]
             (matrix-rec
              middle-motive
              (function/lam
               [['current-right matrix-type]]
               (let [right-motive
                     (function/lam
                      [['candidate matrix-type]]
                      (function/forall
                       [['current-left-middle
                         (matrix-same-shape empty empty)]
                        ['current-middle-right
                         (matrix-same-shape empty 'candidate)]]
                       (matrix-same-shape empty 'candidate)))]
                 (matrix-rec
                   right-motive
                   (function/lam
                    [['current-left-middle
                      (matrix-same-shape empty empty)]
                     ['current-middle-right
                      (matrix-same-shape empty empty)]]
                    trivial)
                   (function/lam
                    [['right-row vector-type] ['right-tail matrix-type]
                     ['ignored (app right-motive 'right-tail)]]
                    (function/lam
                     [['current-left-middle
                       (matrix-same-shape empty empty)]
                      ['current-middle-right
                       (matrix-same-shape
                        empty (cons-matrix 'right-row 'right-tail))]]
                     (absurd
                      (matrix-same-shape
                       empty (cons-matrix 'right-row 'right-tail))
                      'current-middle-right)))
                   'current-right)))
              (function/lam
               [['middle-row vector-type] ['middle-tail matrix-type]
                ['ignored (app middle-motive 'middle-tail)]]
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-same-shape
                   empty (cons-matrix 'middle-row 'middle-tail))]
                 ['current-middle-right
                  (matrix-same-shape
                   (cons-matrix 'middle-row 'middle-tail)
                   'current-right)]]
                (absurd
                 (matrix-same-shape empty 'current-right)
                 'current-left-middle)))
              'current-middle)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-transitive (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle matrix-type]]
                  (function/forall
                   [['current-right matrix-type]
                    ['current-left-middle
                     (matrix-same-shape current-left 'current-middle)]
                    ['current-middle-right
                     (matrix-same-shape 'current-middle 'current-right)]]
                   (matrix-same-shape current-left 'current-right)))]
             (function/lam
              [['current-middle matrix-type]]
              (matrix-rec
               middle-motive
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-same-shape current-left (nil-matrix))]
                 ['current-middle-right
                  (matrix-same-shape (nil-matrix) 'current-right)]]
                (absurd
                 (matrix-same-shape current-left 'current-right)
                 'current-left-middle))
               (function/lam
                [['middle-row vector-type] ['middle-tail matrix-type]
                 ['ignored-middle (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-matrix 'middle-row 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right matrix-type]]
                       (function/forall
                        [['current-left-middle
                          (matrix-same-shape current-left current-middle)]
                         ['current-middle-right
                          (matrix-same-shape current-middle 'current-right)]]
                        (matrix-same-shape current-left 'current-right)))]
                  (function/lam
                   [['current-right matrix-type]]
                   (matrix-rec
                    right-motive
                    (function/lam
                     [['current-left-middle
                       (matrix-same-shape current-left current-middle)]
                      ['current-middle-right
                       (matrix-same-shape current-middle (nil-matrix))]]
                     (absurd
                      (matrix-same-shape current-left (nil-matrix))
                      'current-middle-right))
                    (function/lam
                     [['right-row vector-type] ['right-tail matrix-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-left-middle
                        (matrix-same-shape current-left current-middle)]
                       ['current-middle-right
                        (matrix-same-shape
                         current-middle
                         (cons-matrix 'right-row 'right-tail))]]
                      (let [left-head-middle
                            (vector-same-shape 'left-row 'middle-row)
                            left-tail-middle
                            (matrix-same-shape 'left-tail 'middle-tail)
                            middle-head-right
                            (vector-same-shape 'middle-row 'right-row)
                            middle-tail-right
                            (matrix-same-shape 'middle-tail 'right-tail)]
                        (conjoin
                         (vector-same-shape 'left-row 'right-row)
                         (matrix-same-shape 'left-tail 'right-tail)
                         (app
                          (function/const* 'vector/same-shape-transitive [])
                          'left-row 'middle-row 'right-row
                          (proposition-left
                           left-head-middle left-tail-middle
                           'current-left-middle)
                          (proposition-left
                           middle-head-right middle-tail-right
                           'current-middle-right))
                         (app 'tail-transitive
                              'middle-tail 'right-tail
                              (proposition-right
                               left-head-middle left-tail-middle
                               'current-left-middle)
                              (proposition-right
                               middle-head-right middle-tail-right
                               'current-middle-right))))))
                    'current-right))))
               'current-middle))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'middle 'right 'left-middle 'middle-right)))})

(def add-preserves-shape-spec
  {:name 'matrix/add-preserves-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (conjunction
     (matrix-same-shape (matrix-addition 'left 'right) 'left)
     (matrix-same-shape (matrix-addition 'left 'right) 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-same-shape 'current-left 'current-right)]]
            (conjunction
             (matrix-same-shape
              (matrix-addition 'current-left 'current-right)
              'current-left)
             (matrix-same-shape
              (matrix-addition 'current-left 'current-right)
              'current-right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-same-shape empty 'current-right)]]
                  (conjunction
                   (matrix-same-shape
                    (matrix-addition empty 'current-right) empty)
                   (matrix-same-shape
                    (matrix-addition empty 'current-right)
                    'current-right))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-same-shape empty empty)]]
               (conjoin
                (matrix-same-shape empty empty)
                (matrix-same-shape empty empty)
                trivial trivial))
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-same-shape
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (conjunction
                  (matrix-same-shape
                   (matrix-addition
                    empty (cons-matrix 'right-row 'right-tail)) empty)
                  (matrix-same-shape
                   (matrix-addition
                    empty (cons-matrix 'right-row 'right-tail))
                   (cons-matrix 'right-row 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-preserves (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-same-shape current-left 'current-right)]]
                   (conjunction
                    (matrix-same-shape
                     (matrix-addition current-left 'current-right)
                     current-left)
                    (matrix-same-shape
                     (matrix-addition current-left 'current-right)
                     'current-right))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (conjunction
                  (matrix-same-shape
                   (matrix-addition current-left (nil-matrix))
                   current-left)
                  (matrix-same-shape
                   (matrix-addition current-left (nil-matrix))
                   (nil-matrix)))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-same-shape
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-shape
                       (vector-same-shape 'left-row 'right-row)
                       tail-shape
                       (matrix-same-shape 'left-tail 'right-tail)
                       head-both
                       (app (function/const* 'vector/add-preserves-shape [])
                            'left-row 'right-row
                            (proposition-left
                             head-shape tail-shape 'current-same))
                       tail-both
                       (app 'tail-preserves 'right-tail
                            (proposition-right
                             head-shape tail-shape 'current-same))
                       head-left
                       (vector-same-shape
                        (vector-add 'left-row 'right-row) 'left-row)
                       head-right
                       (vector-same-shape
                        (vector-add 'left-row 'right-row) 'right-row)
                       tail-left
                       (matrix-same-shape
                        (matrix-addition 'left-tail 'right-tail)
                        'left-tail)
                       tail-right
                       (matrix-same-shape
                        (matrix-addition 'left-tail 'right-tail)
                        'right-tail)]
                   (conjoin
                    (matrix-same-shape
                     (matrix-addition
                      current-left
                      (cons-matrix 'right-row 'right-tail))
                     current-left)
                    (matrix-same-shape
                     (matrix-addition
                      current-left
                      (cons-matrix 'right-row 'right-tail))
                     (cons-matrix 'right-row 'right-tail))
                    (conjoin
                     head-left tail-left
                     (proposition-left head-left head-right head-both)
                     (proposition-left tail-left tail-right tail-both))
                    (conjoin
                     head-right tail-right
                     (proposition-right head-left head-right head-both)
                     (proposition-right tail-left tail-right tail-both))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def definition-specs [])
(def theorem-specs
  [same-shape-symmetric-spec
   same-shape-transitive-spec
   add-preserves-shape-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      matrix-add/extend-environment
      (support/extend-with :finite-matrix-add-shape theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
