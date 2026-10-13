(ns rainbow.algorithms.proofs.feature-importance
  "AHoF V54 Permutation Feature Importance: the drop in model score when a
  feature's values are permuted, measuring how much the model relies on it:

      importance(feature) = baseline-score - permuted-score

  a signed subtraction (the drop is usually positive but can be negative for a
  harmful feature). Worked instances prove the drop on the signed equivalence.
  The scoring function, the permutation, and the averaging over repetitions are
  the executable concern.

  Requires the signed rationals in the environment.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.feature-importance`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-subtract [l r]
  (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- signed-cross [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

(defn- importance [baseline permuted]
  (function/app (function/const* 'importance/importance []) baseline permuted))

;; Definitions --------------------------------------------------------------

;; importance = baseline-score - permuted-score
(def importance-spec
  {:name 'importance/importance :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['baseline signed] ['permuted signed]]
                        (signed-subtract 'baseline 'permuted))})

(def definition-specs [importance-spec])

;; Theorems -----------------------------------------------------------------

(def importance-unfold-spec
  {:name 'importance/importance-unfold :universes []
   :type (function/forall
          [['baseline signed] ['permuted signed]]
          (equality signed (importance 'baseline 'permuted)
                    (signed-subtract 'baseline 'permuted)))
   :value (function/lam [['baseline signed] ['permuted signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (importance 'baseline 'permuted)))})

;; A feature the model relies on: score drops 5 -> 3, importance 2.
(def relied-on-example-spec
  {:name 'importance/relied-on-example :universes []
   :type (signed-equivalent (importance (signed-numeral 5) (signed-numeral 3))
                            (signed-numeral 2))
   :value (signed-cross (importance (signed-numeral 5) (signed-numeral 3))
                        (signed-numeral 2))})

;; An unused feature: the score is unchanged, importance 0.
(def unused-example-spec
  {:name 'importance/unused-example :universes []
   :type (signed-equivalent (importance (signed-numeral 4) (signed-numeral 4))
                            (signed-numeral 0))
   :value (signed-cross (importance (signed-numeral 4) (signed-numeral 4))
                        (signed-numeral 0))})

(def theorem-specs [importance-unfold-spec relied-on-example-spec
                    unused-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :feature-importance
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
