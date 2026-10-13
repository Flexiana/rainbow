(ns rainbow.algorithms.proofs.counterfactual-distance-separation
  "Native separation laws for the existing counterfactual squared distance.

    signed/subtract-zero-reflects-equivalence
    vector/subtract-zero-reflects-equivalence
    counterfactual/distance-squared-nonnegative
    counterfactual/equivalent-of-distance-squared-zero

  Vector subtraction truncates, so separation explicitly requires equal shape.
  Under that hypothesis, zero squared distance reflects each component through
  signed subtraction and yields vector/equivalent.  Native and axiom-free."
  (:require [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.counterfactual :as counterfactual]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.rational :as signed-rational]
            [rainbow.math.linear.vector.norm-zero-reflection :as norm-reflection]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- distance-squared [left right]
  (app (function/const* 'counterfactual/distance-squared []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- nonnegative [value]
  (app (function/const* 'signed/nonnegative []) value))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- absurd [target impossible]
  (app impossible target))

(def subtract-zero-reflects-equivalence-spec
  {:name 'signed/subtract-zero-reflects-equivalence :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['difference-zero
      (signed-equivalent
       (signed-subtract 'left 'right) signed-zero)]]
    (signed-equivalent 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['difference-zero
      (signed-equivalent
       (signed-subtract 'left 'right) signed-zero)]]
    (let [pl (positive 'left) nl (negative 'left)
          pr (positive 'right) nr (negative 'right)
          start (radd pl nr)
          padded-left (radd start nnrat-zero)
          padded-right (radd nnrat-zero (radd nl pr))
          raw-right (radd nl pr)
          finish (radd pr nl)]
      (rat-transitive
       start padded-left finish
       (rat-symmetric
        padded-left start
        (app (function/const* 'nnrat/add-zero-right []) start))
       (rat-transitive
        padded-left padded-right finish
        'difference-zero
        (rat-transitive
         padded-right raw-right finish
         (app (function/const* 'nnrat/add-zero-left []) raw-right)
         (app (function/const* 'nnrat/add-commutative []) nl pr))))))})

(def subtract-zero-reflects-vector-equivalence-spec
  {:name 'vector/subtract-zero-reflects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['difference-zero
      (vector-equivalent
       (vector-subtract 'left 'right)
       (zero-like (vector-subtract 'left 'right)))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['difference-zero
      (vector-equivalent
       (vector-subtract 'left 'right)
       (zero-like (vector-subtract 'left 'right)))]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-shape
              (same-shape 'current-left 'current-right)]
             ['current-difference-zero
              (vector-equivalent
               (vector-subtract 'current-left 'current-right)
               (zero-like
                (vector-subtract 'current-left 'current-right)))]]
            (vector-equivalent 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-shape
                    (same-shape empty 'current-right)]
                   ['current-difference-zero
                    (vector-equivalent
                     (vector-subtract empty 'current-right)
                     (zero-like
                      (vector-subtract empty 'current-right)))]]
                  (vector-equivalent empty 'current-right)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-shape (same-shape empty empty)]
                ['current-difference-zero
                 (vector-equivalent
                  (vector-subtract empty empty)
                  (zero-like (vector-subtract empty empty)))]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (let [current-right
                     (cons-vector 'right-head 'right-tail)]
                 (function/lam
                  [['current-shape
                    (same-shape empty current-right)]
                   ['current-difference-zero
                    (vector-equivalent
                     (vector-subtract empty current-right)
                     (zero-like
                      (vector-subtract empty current-right)))]]
                  (absurd
                   (vector-equivalent empty current-right)
                   'current-shape))))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-reflection (app outer-motive 'left-tail)]]
           (let [current-left
                 (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-shape
                     (same-shape current-left 'current-right)]
                    ['current-difference-zero
                     (vector-equivalent
                      (vector-subtract current-left 'current-right)
                      (zero-like
                       (vector-subtract current-left 'current-right)))]]
                   (vector-equivalent current-left 'current-right)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-shape
                  (same-shape current-left (nil-vector))]
                 ['current-difference-zero
                  (vector-equivalent
                   (vector-subtract current-left (nil-vector))
                   (zero-like
                    (vector-subtract current-left (nil-vector))))]]
                (absurd
                 (vector-equivalent current-left (nil-vector))
                 'current-shape))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (let [current-right
                      (cons-vector 'right-head 'right-tail)]
                  (function/lam
                   [['current-shape
                     (same-shape current-left current-right)]
                    ['current-difference-zero
                     (vector-equivalent
                      (vector-subtract current-left current-right)
                      (zero-like
                       (vector-subtract current-left current-right)))]]
                   (let [head-shape
                         (signed-equivalent signed-zero signed-zero)
                         tail-shape
                         (same-shape 'left-tail 'right-tail)
                         tail-same-shape
                         (proposition-right
                          head-shape tail-shape 'current-shape)
                         head-difference
                         (signed-subtract 'left-head 'right-head)
                         tail-difference
                         (vector-subtract 'left-tail 'right-tail)
                         head-difference-zero
                         (proposition-left
                          (signed-equivalent
                           head-difference signed-zero)
                          (vector-equivalent
                           tail-difference (zero-like tail-difference))
                          'current-difference-zero)
                         tail-difference-zero
                         (proposition-right
                          (signed-equivalent
                           head-difference signed-zero)
                          (vector-equivalent
                           tail-difference (zero-like tail-difference))
                          'current-difference-zero)
                         head-same
                         (app
                          (function/const*
                           'signed/subtract-zero-reflects-equivalence [])
                          'left-head 'right-head head-difference-zero)
                         tail-same
                         (app 'tail-reflection 'right-tail
                              tail-same-shape tail-difference-zero)]
                     (conjoin
                      (signed-equivalent 'left-head 'right-head)
                      (vector-equivalent 'left-tail 'right-tail)
                      head-same tail-same)))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'shape 'difference-zero)))})

(def distance-squared-nonnegative-spec
  {:name 'counterfactual/distance-squared-nonnegative :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (nonnegative (distance-squared 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (app (function/const* 'norm/norm-squared-nonnegative [])
         (vector-subtract 'left 'right)))})

(def equivalent-of-distance-squared-zero-spec
  {:name 'counterfactual/equivalent-of-distance-squared-zero :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['distance-zero
      (signed-equivalent
       (distance-squared 'left 'right) signed-zero)]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['distance-zero
      (signed-equivalent
       (distance-squared 'left 'right) signed-zero)]]
    (let [difference (vector-subtract 'left 'right)
          difference-zero
          (app
           (function/const*
            'norm/equivalent-zero-like-of-norm-squared-zero [])
           difference 'distance-zero)]
      (app
       (function/const* 'vector/subtract-zero-reflects-equivalence [])
       'left 'right 'shape difference-zero)))})

(def definition-specs [])
(def theorem-specs
  [subtract-zero-reflects-equivalence-spec
   subtract-zero-reflects-vector-equivalence-spec
   distance-squared-nonnegative-spec
   equivalent-of-distance-squared-zero-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      norm-reflection/extend-environment
      (extend-spec-if-missing
       'signed/subtract :signed-rational signed-rational/subtract-spec)
      (extend-spec-if-missing
       'vector/negate :finite-vector finite-vector/negate-spec)
      (extend-spec-if-missing
       'vector/add :finite-vector finite-vector/add-spec)
      (extend-spec-if-missing
       'vector/subtract :finite-vector finite-vector/subtract-spec)
      (extend-spec-if-missing
       'vector/same-shape :vector-shape-cancellation shape/same-shape-spec)
      (extend-spec-if-missing
       'counterfactual/distance-squared :counterfactual
       counterfactual/distance-squared-spec)
      (support/extend-with :counterfactual-distance-separation theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
