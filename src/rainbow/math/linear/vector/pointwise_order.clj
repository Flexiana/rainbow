(ns rainbow.math.linear.vector.pointwise-order
  "Length-sensitive componentwise order for signed-rational vectors.

    vector/at-most [] []             = Truth
    vector/at-most [] (y :: ys)      = Falsity
    vector/at-most (x :: xs) []      = Falsity
    vector/at-most (x :: xs) (y :: ys)
      = signed/at-most x y AND vector/at-most xs ys

  The definition turns scalar order certificates into a native finite-vector
  feasibility relation.  Reflexivity and uniform-clamp monotonicity are proved
  structurally, without adding axioms or changing the kernel.

  This is deliberately distinct from signed/all-at-most: that theorem compares
  two functions on an explicit list of problem indices, while vector/at-most
  compares two native value lists by position and makes equal dimension part of
  the proposition."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.uniform-clamp :as uniform-clamp]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- list-prop [motive base step values]
  (app (function/const* 'data/List.rec [type-level type-level])
       signed motive base step values))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- clamp [lower upper value]
  (app (function/const* 'signed/clamp []) lower upper value))
(defn- uniform-project [lower upper values]
  (app (function/const* 'vector/uniform-clamp []) lower upper values))

(def truth (function/const* 'proposition/truth []))
(def falsity (function/const* 'proposition/falsity []))
(def trivial (function/const* 'proposition/trivial []))

(def vector-at-most-spec
  {:name 'vector/at-most :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type 'Prop)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam
       [['ignored vector-type]]
       (function/arrow vector-type 'Prop))
      (function/lam
       [['current-right vector-type]]
       (list-prop
        (function/lam [['ignored vector-type]] 'Prop)
        truth
        (function/lam
         [['right-head signed] ['right-tail vector-type]
          ['ignored 'Prop]]
         falsity)
        'current-right))
      (function/lam
       [['left-head signed] ['left-tail vector-type]
        ['tail-relation (function/arrow vector-type 'Prop)]]
       (function/lam
        [['current-right vector-type]]
        (list-prop
         (function/lam [['ignored vector-type]] 'Prop)
         falsity
         (function/lam
          [['right-head signed] ['right-tail vector-type]
           ['ignored 'Prop]]
          (conjunction
           (at-most 'left-head 'right-head)
           (app 'tail-relation 'right-tail)))
         'current-right)))
      'left)
     'right))})

(def at-most-empty-spec
  {:name 'vector/at-most-empty :universes []
   :type (vector-at-most (nil-vector) (nil-vector))
   :value trivial})

(def at-most-cons-spec
  {:name 'vector/at-most-cons :universes []
   :type
   (function/forall
    [['left-head signed] ['right-head signed]
     ['left-tail vector-type] ['right-tail vector-type]
     ['head-ordered (at-most 'left-head 'right-head)]
     ['tail-ordered (vector-at-most 'left-tail 'right-tail)]]
    (vector-at-most
     (cons-vector 'left-head 'left-tail)
     (cons-vector 'right-head 'right-tail)))
   :value
   (function/lam
    [['left-head signed] ['right-head signed]
     ['left-tail vector-type] ['right-tail vector-type]
     ['head-ordered (at-most 'left-head 'right-head)]
     ['tail-ordered (vector-at-most 'left-tail 'right-tail)]]
    (conjoin (at-most 'left-head 'right-head)
             (vector-at-most 'left-tail 'right-tail)
             'head-ordered 'tail-ordered))})

(def at-most-reflexive-spec
  {:name 'vector/at-most-reflexive :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-at-most 'values 'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-at-most 'current 'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-reflexive (vector-at-most 'tail 'tail)]]
           (conjoin
            (at-most 'head 'head)
            (vector-at-most 'tail 'tail)
            (app (function/const* 'signed/at-most-reflexive []) 'head)
            'tail-reflexive))]
      (list-rec motive trivial step 'values)))})

(def uniform-clamp-monotone-spec
  {:name 'vector/uniform-clamp-monotone :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (uniform-project 'lower 'upper 'left)
     (uniform-project 'lower 'upper 'right)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (uniform-project 'lower 'upper 'current-left)
             (uniform-project 'lower 'upper 'current-right))))
          base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (uniform-project 'lower 'upper empty)
                   (uniform-project 'lower 'upper 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              inner-motive
              (function/lam
               [['current-ordered (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app inner-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-ordered))
              'current-right)))
          step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (uniform-project 'lower 'upper current-left)
                    (uniform-project 'lower 'upper 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               inner-motive
               (function/lam
                [['current-ordered
                  (vector-at-most current-left (nil-vector))]]
                'current-ordered)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app inner-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (vector-at-most
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-order (at-most 'left-head 'right-head)
                       tail-order (vector-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (at-most (clamp 'lower 'upper 'left-head)
                             (clamp 'lower 'upper 'right-head))
                    (vector-at-most
                     (uniform-project 'lower 'upper 'left-tail)
                     (uniform-project 'lower 'upper 'right-tail))
                    (app (function/const* 'signed/clamp-monotone [])
                         'lower 'upper 'left-head 'right-head
                         (proposition-left head-order tail-order
                                           'current-ordered))
                    (app 'tail-monotone 'right-tail
                         (proposition-right head-order tail-order
                                            'current-ordered))))))
               'current-right))))]
      (app (list-rec outer-motive base step 'left)
           'right 'ordered)))})

(def definition-specs [vector-at-most-spec])
(def theorem-specs
  [at-most-empty-spec at-most-cons-spec at-most-reflexive-spec
   uniform-clamp-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniform-clamp/extend-environment
      (support/extend-with :vector-pointwise-order
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
