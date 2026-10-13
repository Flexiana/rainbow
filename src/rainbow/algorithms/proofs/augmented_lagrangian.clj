(ns rainbow.algorithms.proofs.augmented-lagrangian
  "AHoF O49 Augmented Lagrangian: the dual multiplier update in the outer loop.
  Where the penalty method (O48) only grows a penalty weight, the augmented
  Lagrangian also maintains a Lagrange multiplier that is updated from the
  measured constraint violation each outer iteration:

      multiplier' = multiplier + rho * constraint

  a signed update (the multiplier and the constraint value may be negative). This
  reuses signed scaling and addition. The inner penalized minimization and the
  augmented-Lagrangian value itself are the executable concern; what is proved is
  the multiplier-update recurrence and worked instances -- a positive violation
  raises the multiplier, an over-satisfied constraint lowers it.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.augmented-lagrangian`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-add [l r] (function/app (function/const* 'signed/add []) l r))
(defn- signed-scale [rate v]
  (function/app (function/const* 'signed/scale []) rate v))
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-num [n] (function/app (function/const* 'nnrat/make [])
                                   (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-num n)))
(defn- signed-make [p n] (function/app (function/const* 'signed/make []) p n))
(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))

(defn- update-multiplier [multiplier rho constraint]
  (function/app (function/const* 'lagrangian/update-multiplier [])
                multiplier rho constraint))

(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

;; multiplier' = multiplier + rho * constraint
(def update-multiplier-spec
  {:name 'lagrangian/update-multiplier :kind :definition :universes []
   :type (function/arrow signed nnrat signed signed)
   :value (function/lam [['multiplier signed] ['rho nnrat]
                         ['constraint signed]]
                        (signed-add 'multiplier
                                    (signed-scale 'rho 'constraint)))})

(def definition-specs [update-multiplier-spec])

;; Theorems -----------------------------------------------------------------

(def update-multiplier-unfold-spec
  {:name 'lagrangian/update-multiplier-unfold :universes []
   :type (function/forall
          [['multiplier signed] ['rho nnrat] ['constraint signed]]
          (equality signed (update-multiplier 'multiplier 'rho 'constraint)
                    (signed-add 'multiplier
                                (signed-scale 'rho 'constraint))))
   :value (function/lam [['multiplier signed] ['rho nnrat] ['constraint signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed
                         (update-multiplier 'multiplier 'rho 'constraint)))})

;; A positive violation raises the multiplier: 1 + 2*1 = 3.
(def violation-raises-example-spec
  {:name 'lagrangian/violation-raises-example :universes []
   :type (signed-equivalent
          (update-multiplier (signed-numeral 1) (nnrat-num 2) (signed-numeral 1))
          (signed-numeral 3))
   :value (signed-cross-reflexivity
           (update-multiplier (signed-numeral 1) (nnrat-num 2) (signed-numeral 1))
           (signed-numeral 3))})

;; An over-satisfied constraint (negative violation) lowers the multiplier:
;; 3 + 1*(-1) = 2.
(def over-satisfied-example-spec
  (let [minus-one (signed-make (nnrat-num 0) (nnrat-num 1))]
    {:name 'lagrangian/over-satisfied-example :universes []
     :type (signed-equivalent
            (update-multiplier (signed-numeral 3) (nnrat-num 1) minus-one)
            (signed-numeral 2))
     :value (signed-cross-reflexivity
             (update-multiplier (signed-numeral 3) (nnrat-num 1) minus-one)
             (signed-numeral 2))}))

(def theorem-specs [update-multiplier-unfold-spec violation-raises-example-spec
                    over-satisfied-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :augmented-lagrangian
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
