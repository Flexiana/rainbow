(ns rainbow.algorithms.proofs.counterfactual
  "AHoF V57 Counterfactual Explanation: the proximity term of the counterfactual
  search objective. A counterfactual for an input is the nearest point that flips
  the model's decision, found by minimizing distance-to-original plus a penalty
  for not achieving the desired class. The distinctive proximity measure is the
  squared distance between the original and the candidate:

      distance-squared = <original - candidate, original - candidate>

  the inner product of the difference with itself. Because the difference is a
  non-origin subtraction (Grothendieck pairs), the worked value is proven on the
  signed equivalence: the counterfactual [1,0] is squared-distance 9 from the
  original [4,0]. The desired-class penalty and the outer minimization stay in
  the executable reference.

  Requires signed multiplication and the vector dot product.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.counterfactual`
  prints this classification."
  (:require [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.algorithms.proofs.inner-product :as dep-inner-product]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-subtract [l r]
  (function/app (function/const* 'vector/subtract []) l r))
(defn- vector-dot [l r] (function/app (function/const* 'vector/dot []) l r))
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

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

(defn- distance-squared [original candidate]
  (function/app (function/const* 'counterfactual/distance-squared [])
                original candidate))

;; Definitions --------------------------------------------------------------

;; distance-squared = <original - candidate, original - candidate>
(def distance-squared-spec
  {:name 'counterfactual/distance-squared :kind :definition :universes []
   :type (function/arrow vector-type vector-type signed)
   :value (function/lam [['original vector-type] ['candidate vector-type]]
                        (let [diff (vector-subtract 'original 'candidate)]
                          (vector-dot diff diff)))})

(def definition-specs [distance-squared-spec])

;; Theorems -----------------------------------------------------------------

;; The counterfactual [1,0] is squared-distance 9 from the original [4,0]:
;; (4-1)^2 + 0^2 = 9. The difference component is the pair (4,1) whose square
;; is (17,8) ~ 9, proven on the signed equivalence.
(def distance-example-spec
  {:name 'counterfactual/distance-example :universes []
   :type (signed-equivalent
          (distance-squared (make-vector (signed-numeral 4) (signed-numeral 0))
                            (make-vector (signed-numeral 1) (signed-numeral 0)))
          (signed-numeral 9))
   :value (signed-cross
           (distance-squared (make-vector (signed-numeral 4) (signed-numeral 0))
                             (make-vector (signed-numeral 1) (signed-numeral 0)))
           (signed-numeral 9))})

;; A closer counterfactual [3,4] has smaller squared distance 2 from [4,5]:
;; (4-3)^2 + (5-4)^2 = 2.
(def closer-example-spec
  {:name 'counterfactual/closer-example :universes []
   :type (signed-equivalent
          (distance-squared (make-vector (signed-numeral 4) (signed-numeral 5))
                            (make-vector (signed-numeral 3) (signed-numeral 4)))
          (signed-numeral 2))
   :value (signed-cross
           (distance-squared (make-vector (signed-numeral 4) (signed-numeral 5))
                             (make-vector (signed-numeral 3) (signed-numeral 4)))
           (signed-numeral 2))})

(def theorem-specs [distance-example-spec closer-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-inner-product/extend-environment (dep-finite-vector/extend-environment checked-environment)) :counterfactual
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
