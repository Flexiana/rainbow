(ns rainbow.algorithms.proofs.ahof.nnls
  "Nonnegative projection for NNLS (Kochenderfer Optimization O13.4), a
  signed-cluster algorithm deferred in August: over nonnegative rationals
  the projection is degenerate, so it needed the signed layer's max(x,0).

  `optimization/nnls-project x = signed/max x signed/zero` clamps a signed
  value up to zero -- the projection onto the nonnegative orthant that each
  NNLS coordinate step applies. Two worked theorems cover both branches:
  a positive value passes through (max 5 0 ~ 5), a negative value projects
  to zero (max -3 0 ~ 0), each by signed cross-product reflexivity. Chains
  signed-minmax for signed/max; native and axiom-free on D63. A proved
  native module; formal ledger crediting is the separate catalog
  follow-up."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as antisymmetry]
            [rainbow.math.rational.signed.minmax :as minmax]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- numeral [n]
  (loop [remaining (long n) term (function/const* 'data/zero [])]
    (if (zero? remaining)
      term
      (recur (dec remaining) (app (function/const* 'data/succ []) term)))))
(defn- nnrat-of [n]
  (app (function/const* 'nnrat/make []) (numeral n)
       (function/const* 'data/zero [])))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- signed-negate [v] (app (function/const* 'signed/negate []) v))
(defn- signed-zero [] (function/const* 'signed/zero []))
(defn- signed-max [a b] (app (function/const* 'signed/max []) a b))
(defn- signed-at-most [a b] (app (function/const* 'signed/at-most []) a b))
(defn- signed-equivalent [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- signed-positive [v] (app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (app (function/const* 'signed/negative []) v))
(defn- nnrat-add [a b] (app (function/const* 'nnrat/add []) a b))
(defn- numerator [v] (app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [a b] (app (function/const* 'nat/multiply []) a b))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (app (function/const* 'equality/reflexive [type-level])
         nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def nnls-project-spec
  {:name 'optimization/nnls-project :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed)
   :value (function/lam [['value signed]]
                        (signed-max 'value (signed-zero)))})

(defn- project [v] (app (function/const* 'optimization/nnls-project []) v))

(def nnls-project-positive-spec
  "A nonnegative value passes through the projection unchanged."
  {:name 'optimization/nnls-project-positive-worked :universes []
   :type (signed-equivalent (project (from-nnrat (nnrat-of 5)))
                            (from-nnrat (nnrat-of 5)))
   :value (signed-equivalent-cross (project (from-nnrat (nnrat-of 5)))
                                   (from-nnrat (nnrat-of 5)))})

(def nnls-project-negative-spec
  "A negative value projects to zero."
  {:name 'optimization/nnls-project-negative-worked :universes []
   :type (signed-equivalent (project (signed-negate (from-nnrat (nnrat-of 3))))
                            (signed-zero))
   :value (signed-equivalent-cross
           (project (signed-negate (from-nnrat (nnrat-of 3))))
           (signed-zero))})

;; The two UNIVERSAL theorems that together define "projection onto the
;; nonnegative orthant": the result is always nonnegative, and every
;; already-nonnegative input is fixed. These upgrade the worked instances
;; above from "correct at these numbers" to all-inputs guarantees.
(def nnls-project-nonnegative-spec
  "For EVERY input the projection is nonnegative -- one application of
  signed/max-upper-right at zero."
  {:name 'optimization/nnls-project-nonnegative :universes []
   :type (function/forall
          [['value signed]]
          (signed-at-most (signed-zero) (project 'value)))
   :value (function/lam
           [['value signed]]
           (app (function/const* 'signed/max-upper-right [])
                'value (signed-zero)))})

(def nnls-project-fixes-nonnegative-spec
  "The projection is the IDENTITY on already-nonnegative inputs: if
  zero <= x then project x ~ x, by antisymmetry of the two max bounds."
  {:name 'optimization/nnls-project-fixes-nonnegative :universes []
   :type (function/forall
          [['value signed]
           ['nonnegative (signed-at-most (signed-zero) 'value)]]
          (signed-equivalent (project 'value) 'value))
   :value (function/lam
           [['value signed]
            ['nonnegative (signed-at-most (signed-zero) 'value)]]
           (app (function/const* 'signed/at-most-antisymmetric [])
                (signed-max 'value (signed-zero)) 'value
                (app (function/const* 'signed/at-most-max [])
                     'value (signed-zero) 'value
                     (app (function/const* 'signed/at-most-reflexive []) 'value)
                     'nonnegative)
                (app (function/const* 'signed/max-upper-left [])
                     'value (signed-zero))))})

(def definition-specs [nnls-project-spec])
(def theorem-specs [nnls-project-positive-spec nnls-project-negative-spec
                    nnls-project-nonnegative-spec
                    nnls-project-fixes-nonnegative-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.minmax])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (antisymmetry/extend-environment) (support/extend-with :ahof-nnls (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.algorithms.proofs.ahof.nnls))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
