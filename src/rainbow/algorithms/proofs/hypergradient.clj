(ns rainbow.algorithms.proofs.hypergradient
  "AHoF O25 Hypergradient Descent: the meta-optimizer that tunes its own
  learning rate by the gradient of the loss with respect to the learning rate.
  That hypergradient is the inner product of the current and previous gradients,
  so the learning-rate update is

      rate' = rate + beta * <gradient_current, gradient_previous>

  built from the vector dot product, signed scaling, and signed addition. When
  successive gradients agree (positive inner product) the rate grows; when they
  are orthogonal it is unchanged. This is the first algorithm to use `vector/dot`.
  The meta-step size beta is a concrete nonnegative rational in the worked
  instances; the base parameter update stays in the executable reference.

  Requires `signed/multiply` and `vector/dot` in the environment.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.hypergradient`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.inner-product :as dep-inner-product]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- vector-dot [left right]
  (function/app (function/const* 'vector/dot []) left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-num [n] (function/app (function/const* 'nnrat/make [])
                                   (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-num n)))
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
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- update-rate [rate beta g-current g-previous]
  (function/app (function/const* 'hypergrad/update-rate [])
                rate beta g-current g-previous))

(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

;; rate' = rate + beta * <g_current, g_previous>
(def update-rate-spec
  {:name 'hypergrad/update-rate :kind :definition :universes []
   :type (function/arrow signed nnrat vector-type vector-type signed)
   :value (function/lam
           [['rate signed] ['beta nnrat]
            ['g-current vector-type] ['g-previous vector-type]]
           (signed-add 'rate
                       (signed-scale 'beta
                                     (vector-dot 'g-current 'g-previous))))})

(def definition-specs [update-rate-spec])

;; Theorems -----------------------------------------------------------------

(def update-rate-unfold-spec
  {:name 'hypergrad/update-rate-unfold :universes []
   :type (function/forall
          [['rate signed] ['beta nnrat]
           ['g-current vector-type] ['g-previous vector-type]]
          (equality signed
                    (update-rate 'rate 'beta 'g-current 'g-previous)
                    (signed-add 'rate
                                (signed-scale 'beta
                                              (vector-dot 'g-current
                                                          'g-previous)))))
   :value (function/lam
           [['rate signed] ['beta nnrat]
            ['g-current vector-type] ['g-previous vector-type]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         signed
                         (update-rate 'rate 'beta 'g-current 'g-previous)))})

;; Aligned gradients grow the rate: rate 1, beta 1, [1,1].[1,1] = 2, so 1+2 = 3.
(def aligned-example-spec
  {:name 'hypergrad/aligned-example :universes []
   :type (signed-equivalent
          (update-rate (signed-numeral 1) (nnrat-num 1)
                       (make-vector (signed-numeral 1) (signed-numeral 1))
                       (make-vector (signed-numeral 1) (signed-numeral 1)))
          (signed-numeral 3))
   :value (signed-cross-reflexivity
           (update-rate (signed-numeral 1) (nnrat-num 1)
                        (make-vector (signed-numeral 1) (signed-numeral 1))
                        (make-vector (signed-numeral 1) (signed-numeral 1)))
           (signed-numeral 3))})

;; Orthogonal gradients leave the rate unchanged: rate 2, [1,0].[0,1] = 0.
(def orthogonal-example-spec
  {:name 'hypergrad/orthogonal-example :universes []
   :type (signed-equivalent
          (update-rate (signed-numeral 2) (nnrat-num 1)
                       (make-vector (signed-numeral 1) (signed-numeral 0))
                       (make-vector (signed-numeral 0) (signed-numeral 1)))
          (signed-numeral 2))
   :value (signed-cross-reflexivity
           (update-rate (signed-numeral 2) (nnrat-num 1)
                        (make-vector (signed-numeral 1) (signed-numeral 0))
                        (make-vector (signed-numeral 0) (signed-numeral 1)))
           (signed-numeral 2))})

(def theorem-specs
  [update-rate-unfold-spec aligned-example-spec orthogonal-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.inner-product])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :hypergradient (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.hypergradient))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
