(ns rainbow.math.rational.signed.add-zero-reflection
  "A zero sum of two nonnegative signed rationals has zero summands.

    signed/add-zero-split-nonnegative-left
    signed/add-zero-split-nonnegative-right

  For the left summand, 0<=b and additive monotonicity give a<=a+b.  If
  a+b~0, transport that bound to a<=0; 0<=a follows from nonnegativity, and
  signed antisymmetry gives a~0.  The right theorem commutes the sum and reuses
  the left theorem.  Native and axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.at-most-cancellation :as nat-cancellation]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]
            [rainbow.math.rational.nnrat.add-monotone :as nnrat-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as reassociation]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as monotone]
            [rainbow.math.rational.signed.order-transitivity :as transitivity]
            [rainbow.math.rational.signed.unit-laws :as unit]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- nonnegative [value]
  (app (function/const* 'signed/nonnegative []) value))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- at-most-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'signed/equivalent-to-at-most [])
       left right same))
(defn- zero-at-most [value proof]
  (app (function/const* 'signed/zero-at-most-of-nonnegative [])
       value proof))

(def add-zero-split-nonnegative-left-spec
  {:name 'signed/add-zero-split-nonnegative-left :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]
     ['sum-zero (equivalent (sadd 'left 'right) signed-zero)]]
    (equivalent 'left signed-zero))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]
     ['sum-zero (equivalent (sadd 'left 'right) signed-zero)]]
    (let [left-plus-zero (sadd 'left signed-zero)
          sum (sadd 'left 'right)
          zero-left (zero-at-most 'left 'left-nonnegative)
          zero-right (zero-at-most 'right 'right-nonnegative)
          left-to-padded
          (equivalent-to-at-most
           'left left-plus-zero
           (equivalent-symmetric
            left-plus-zero 'left
            (app (function/const* 'signed/add-zero-right []) 'left)))
          padded-to-sum
          (app (function/const* 'signed/add-left-monotone [])
               signed-zero 'right 'left zero-right)
          left-to-sum
          (at-most-transitive
           'left left-plus-zero sum left-to-padded padded-to-sum)
          sum-to-zero
          (equivalent-to-at-most sum signed-zero 'sum-zero)
          left-to-zero
          (at-most-transitive
           'left sum signed-zero left-to-sum sum-to-zero)]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'left signed-zero left-to-zero zero-left)))})

(def add-zero-split-nonnegative-right-spec
  {:name 'signed/add-zero-split-nonnegative-right :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]
     ['sum-zero (equivalent (sadd 'left 'right) signed-zero)]]
    (equivalent 'right signed-zero))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]
     ['sum-zero (equivalent (sadd 'left 'right) signed-zero)]]
    (let [right-plus-zero (sadd 'right signed-zero)
          reordered (sadd 'right 'left)
          sum (sadd 'left 'right)
          zero-right (zero-at-most 'right 'right-nonnegative)
          zero-left (zero-at-most 'left 'left-nonnegative)
          right-to-padded
          (equivalent-to-at-most
           'right right-plus-zero
           (equivalent-symmetric
            right-plus-zero 'right
            (app (function/const* 'signed/add-zero-right []) 'right)))
          padded-to-reordered
          (app (function/const* 'signed/add-left-monotone [])
               signed-zero 'left 'right zero-left)
          reordered-to-sum
          (equivalent-to-at-most
           reordered sum
           (app (function/const* 'signed/add-commutative [])
                'right 'left))
          right-to-reordered
          (at-most-transitive
           'right right-plus-zero reordered
           right-to-padded padded-to-reordered)
          right-to-sum
          (at-most-transitive
           'right reordered sum right-to-reordered reordered-to-sum)
          sum-to-zero
          (equivalent-to-at-most sum signed-zero 'sum-zero)
          right-to-zero
          (at-most-transitive
           'right sum signed-zero right-to-sum sum-to-zero)]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'right signed-zero right-to-zero zero-right)))})

(def definition-specs [])
(def theorem-specs
  [add-zero-split-nonnegative-left-spec
   add-zero-split-nonnegative-right-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/equivalent-symmetric :signed-equivalence-laws equivalence/equivalent-symmetric-spec) (extend-spec-if-missing 'nnrat/add-commutative :nnrat-commutative commutative/add-commutative-spec) (extend-spec-if-missing 'signed/add-commutative :nnrat-commutative commutative/signed-add-commutative-spec) (extend-spec-if-missing 'signed/equivalent-to-at-most :signed-unit-laws unit/equivalent-to-at-most-spec) (extend-spec-if-missing 'signed/zero-at-most-of-nonnegative :signed-multiply-order multiply-order/zero-at-most-of-nonnegative-spec) (extend-spec-if-missing 'nat/at-most-add-right-cancel :nat-at-most-cancellation nat-cancellation/add-right-cancel-spec) (extend-spec-if-missing 'nat/at-most-add-left-cancel :nat-at-most-cancellation nat-cancellation/add-left-cancel-order-spec) (extend-spec-if-missing 'nat/sum-zero-left :nat-at-most-cancellation nat-cancellation/sum-zero-left-spec) (extend-spec-if-missing 'nat/at-most-multiply-right-cancel :nat-at-most-cancellation nat-cancellation/multiply-right-cancel-spec) (extend-spec-if-missing 'nnrat/base-at-most-transitive :nnrat-order-equivalence order-equivalence/base-transitive-spec) (extend-spec-if-missing 'nnrat/at-most-to-cross :nnrat-order-equivalence order-equivalence/at-most-to-cross-spec) (extend-spec-if-missing 'nnrat/base-at-most-add-right-cancel :nnrat-add-cancellation cancellation/base-add-cancel-spec) (extend-spec-if-missing 'nnrat/at-most-add-right-cancel :nnrat-add-cancellation cancellation/add-right-cancel-spec) (extend-spec-if-missing 'nnrat/add-associative :nnrat-additive-reassociation reassociation/add-associative-spec) (extend-spec-if-missing 'nnrat/add-four-reorder :nnrat-additive-reassociation reassociation/add-four-reorder-spec) (extend-spec-if-missing 'nnrat/add-right-monotone-base :nnrat-add-monotone nnrat-monotone/add-right-monotone-base-spec) (extend-spec-if-missing 'nnrat/add-right-monotone :nnrat-add-monotone nnrat-monotone/add-right-monotone-spec) (extend-spec-if-missing 'nnrat/add-left-monotone :nnrat-add-monotone nnrat-monotone/add-left-monotone-spec) (extend-spec-if-missing 'nnrat/add-monotone :nnrat-add-monotone nnrat-monotone/add-monotone-spec) (extend-spec-if-missing 'signed/at-most-transitive :signed-order-transitivity transitivity/at-most-transitive-spec) (extend-spec-if-missing 'signed/add-left-monotone :signed-order-monotone monotone/add-left-monotone-spec) (extend-spec-if-missing 'nnrat/add-zero-right :nnrat-identities identities/add-zero-right-spec) (extend-spec-if-missing 'signed/add-zero-right :signed-limit-uniqueness uniqueness/signed-add-zero-right-spec) (extend-spec-if-missing 'signed/at-most-antisymmetric :signed-limit-uniqueness uniqueness/signed-at-most-antisymmetric-spec) (support/extend-with :signed-add-zero-reflection theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.add-zero-reflection))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
