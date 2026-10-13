(ns rainbow.math.rational.nnrat.order-nontrivial
  "Constructive impossibility of 1 <= 0 and of k+1 <= k+0 in nnrat order.
  These give reusable negative certificates for infeasible constant LP rows.
  The first proof extracts a natural slack from cross-product order and derives
  successor(extra)=0. The second cancels the arbitrary common summand k.
  No classical principle or new axiom is used."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.logic.proposition :as p]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as monotone]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(def ^:private tl [:succ [:zero]])
(def ^:private R (f/const* 'nnrat/NonnegativeRational []))
(def ^:private N (f/const* 'data/Nat []))
(def ^:private zero (f/const* 'nnrat/zero []))
(def ^:private one (f/const* 'nnrat/one []))
(def ^:private nz (f/const* 'data/zero []))
(def ^:private n1 (app 'data/succ nz))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- add [a b] (app 'nnrat/add a b))

(def one-not-at-most-zero-spec
  {:name 'nnrat/one-not-at-most-zero
   :universes []
   :type (p/negation (le one zero))
   :value
   (f/lam
    [['ordered (le one zero)]]
    (let [slack-predicate
          (f/lam [['extra N]]
                 (f/equality tl N (app 'algebra/nat-add n1 'extra) nz))]
      (f/app
       (f/const* 'proposition/use-witness [tl]) N slack-predicate (p/falsity)
       (app 'nnrat/at-most-to-cross one zero 'ordered)
       (f/lam
        [['extra N] ['same (f/equality tl N (app 'algebra/nat-add n1 'extra) nz)]]
        (app 'nat/zero-not-successor 'extra
             (f/app (f/const* 'equality/symmetric [tl]) N
                    (app 'data/succ 'extra) nz 'same))))))})

(def common-add-unit-gap-impossible-spec
  {:name 'nnrat/common-add-unit-gap-impossible
   :universes []
   :type (f/forall [['k R]] (p/negation (le (add 'k one) (add 'k zero))))
   :value
   (f/lam
    [['k R] ['ordered (le (add 'k one) (add 'k zero))]]
    (app 'nnrat/one-not-at-most-zero
         (app 'nnrat/at-most-add-right-cancel one 'k zero
              (app 'nnrat/at-most-respects-equivalence
                   (add one 'k) (add 'k one) (add zero 'k) (add 'k zero)
                   (app 'nnrat/add-commutative one 'k)
                   (app 'nnrat/add-commutative zero 'k)
                   'ordered))))})

(def definition-specs [])
(def theorem-specs [one-not-at-most-zero-spec common-add-unit-gap-impossible-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-order-nontrivial theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.order-nontrivial))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
