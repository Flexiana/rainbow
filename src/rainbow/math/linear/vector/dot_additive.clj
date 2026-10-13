(ns rainbow.math.linear.vector.dot-additive
  "Additivity of the native dot product in its first vector argument.

    same-shape left right
      -> dot (left + right) weights ~ dot left weights + dot right weights

  The shape premise is necessary because vector/add is a truncating zip.  A
  native two-list induction eliminates mismatched inputs; the cons/cons case
  splits on weights and combines signed multiplication distributivity, the tail
  induction hypothesis, and signed four-term reordering."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product-reassoc]
            [rainbow.math.rational.signed.distributive :as signed-distributive]
            [rainbow.math.rational.signed.equivalence-laws :as signed-equivalence]
            [rainbow.math.rational.signed.limit-uniqueness :as signed-zero]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-add]
            [rainbow.math.rational.signed.multiply :as signed-multiply]
            [rainbow.math.linear.vector.shape-add :as shape-add]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
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
(defn- signed-addition [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-product [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(defn- additive-goal [left right weights]
  (signed-equivalent
   (dot (vector-add left right) weights)
   (signed-addition (dot left weights) (dot right weights))))

(defn- zero-additive []
  (let [doubled (signed-addition signed-zero signed-zero)
        doubled-zero
        (app (function/const* 'signed/add-zero-right []) signed-zero)]
    (app (function/const* 'signed/equivalent-symmetric [])
         doubled signed-zero doubled-zero)))

(def dot-additive-left-spec
  {:name 'vector/dot-additive-left :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['same (same-shape 'left 'right)]]
    (additive-goal 'left 'right 'weights))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['same (same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-weights vector-type]
             ['current-same
              (same-shape 'current-left 'current-right)]]
            (additive-goal
             'current-left 'current-right 'current-weights)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-weights vector-type]
                   ['current-same (same-shape empty 'current-right)]]
                  (additive-goal empty 'current-right 'current-weights)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-weights vector-type]
                ['current-same (same-shape empty empty)]]
               (zero-additive))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-weights vector-type]
                 ['current-same
                  (same-shape
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (additive-goal
                  empty (cons-vector 'right-head 'right-tail)
                  'current-weights)
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-additive (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-weights vector-type]
                    ['current-same
                     (same-shape current-left 'current-right)]]
                   (additive-goal
                    current-left 'current-right 'current-weights)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-weights vector-type]
                 ['current-same
                  (same-shape current-left (nil-vector))]]
                (absurd
                 (additive-goal
                  current-left (nil-vector) 'current-weights)
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored-right (app right-motive 'right-tail)]]
                (let [head-zero
                      (signed-equivalent signed-zero signed-zero)
                      tail-shape (same-shape 'left-tail 'right-tail)]
                  (function/lam
                   [['current-weights vector-type]
                    ['current-same
                     (same-shape
                      current-left
                      (cons-vector 'right-head 'right-tail))]]
                   (let [tail-same
                         (proposition-right
                          head-zero tail-shape 'current-same)
                         weight-motive
                         (function/lam
                          [['current-weight vector-type]]
                          (additive-goal
                           current-left
                           (cons-vector 'right-head 'right-tail)
                           'current-weight))]
                     (list-rec
                      weight-motive
                      (zero-additive)
                      (function/lam
                       [['weight-head signed] ['weight-tail vector-type]
                        ['ignored-weight
                         (app weight-motive 'weight-tail)]]
                       (let [left-product
                             (signed-product 'left-head 'weight-head)
                             right-product
                             (signed-product 'right-head 'weight-head)
                             combined-product
                             (signed-product
                              (signed-addition 'left-head 'right-head)
                              'weight-head)
                             combined-tail
                             (dot
                              (vector-add 'left-tail 'right-tail)
                              'weight-tail)
                             left-tail-dot
                             (dot 'left-tail 'weight-tail)
                             right-tail-dot
                             (dot 'right-tail 'weight-tail)
                             start
                             (signed-addition
                              combined-product combined-tail)
                             middle
                             (signed-addition
                              (signed-addition left-product right-product)
                              (signed-addition
                               left-tail-dot right-tail-dot))
                             finish
                             (signed-addition
                              (signed-addition left-product left-tail-dot)
                              (signed-addition right-product right-tail-dot))
                             split
                             (app
                              (function/const*
                               'signed/add-respects-equivalence [])
                              combined-product
                              (signed-addition left-product right-product)
                              combined-tail
                              (signed-addition
                               left-tail-dot right-tail-dot)
                              (app
                               (function/const*
                                'signed/multiply-distributes-add-right [])
                               'left-head 'right-head 'weight-head)
                              (app 'tail-additive
                                   'right-tail 'weight-tail tail-same))
                             reorder
                             (app
                              (function/const* 'signed/add-four-reorder [])
                              left-product right-product
                              left-tail-dot right-tail-dot)]
                         (app
                          (function/const* 'signed/equivalent-transitive [])
                          start middle finish split reorder)))
                      'current-weights)))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'weights 'same)))})

(def definition-specs [])
(def theorem-specs [dot-additive-left-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   checked-environment
   specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      shape-add/extend-environment
      signed-multiply/extend-environment
      (extend-specs-if-missing
       :nnrat-add-monotone add-monotone/theorem-specs)
      (extend-specs-if-missing
       :nnrat-multiply-commute multiply-commute/theorem-specs)
      (extend-specs-if-missing
       :nnrat-product-reassociation product-reassoc/theorem-specs)
      (extend-specs-if-missing
       :nnrat-additive-reassociation add-reassoc/theorem-specs)
      (extend-specs-if-missing
       :nnrat-distribute-right distribute/theorem-specs)
      (extend-spec-if-missing
       'signed/equivalent-symmetric :signed-equivalence-laws
       signed-equivalence/equivalent-symmetric-spec)
      (extend-spec-if-missing
       'signed/add-zero-right :signed-limit-uniqueness
       signed-zero/signed-add-zero-right-spec)
      (extend-spec-if-missing
       'signed/add-respects-equivalence :signed-map-sum-algebra
       signed-add/add-respects-equivalence-spec)
      (extend-spec-if-missing
       'signed/add-four-reorder :signed-map-sum-algebra
       signed-add/add-four-reorder-spec)
      (extend-spec-if-missing
       'signed/equivalent-transitive :signed-map-sum-algebra
       signed-add/equivalent-transitive-spec)
      (extend-spec-if-missing
       'signed/multiply-distributes-add-right :signed-distributive
       signed-distributive/multiply-distributes-add-right-spec)
      inner/extend-environment
      (support/extend-with :vector-dot-additive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
