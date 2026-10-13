(ns rainbow.math.linear.vector.dot-commutative
  "Commutativity of the native truncating signed-vector dot product.

    dot left right  ~  dot right left

  If either list is empty both orientations reduce to signed zero.  The
  cons/cons case combines signed multiplication commutativity at the head with
  the tail induction hypothesis through signed addition congruence.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product-reassoc]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-add]
            [rainbow.math.rational.signed.multiply :as signed-multiply]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-addition [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-product [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))

(def dot-commutative-spec
  {:name 'vector/dot-commutative :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (signed-equivalent (dot 'left 'right) (dot 'right 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (signed-equivalent
             (dot 'current-left 'current-right)
             (dot 'current-right 'current-left))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (signed-equivalent
                  (dot empty 'current-right)
                  (dot 'current-right empty)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (app (function/const* 'signed/equivalent-reflexive [])
                   signed-zero)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (app (function/const* 'signed/equivalent-reflexive [])
                    signed-zero))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-commutes (app outer-motive 'left-tail)]]
           (let [current-left
                 (app (function/const* 'data/cons [type-level])
                      signed 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (signed-equivalent
                   (dot current-left 'current-right)
                   (dot 'current-right current-left)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (app (function/const* 'signed/equivalent-reflexive [])
                    signed-zero)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (app
                 (function/const* 'signed/add-respects-equivalence [])
                 (signed-product 'left-head 'right-head)
                 (signed-product 'right-head 'left-head)
                 (dot 'left-tail 'right-tail)
                 (dot 'right-tail 'left-tail)
                 (app (function/const* 'signed/multiply-commutative [])
                      'left-head 'right-head)
                 (app 'tail-commutes 'right-tail)))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right)))})

(def definition-specs [])
(def theorem-specs [dot-commutative-spec])

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

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-specs-if-missing :nnrat-add-monotone add-monotone/theorem-specs) (extend-specs-if-missing :nnrat-multiply-commute multiply-commute/theorem-specs) (extend-specs-if-missing :nnrat-product-reassociation product-reassoc/theorem-specs) (extend-specs-if-missing :nnrat-additive-reassociation add-reassoc/theorem-specs) (extend-specs-if-missing :nnrat-distribute-right distribute/theorem-specs) (extend-spec-if-missing 'signed/multiply-commutative :signed-multiply-ring signed-ring/multiply-commutative-spec) (extend-spec-if-missing 'signed/add-respects-equivalence :signed-map-sum-algebra signed-add/add-respects-equivalence-spec) inner/extend-environment (support/extend-with :vector-dot-commutative theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.dot-commutative))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
