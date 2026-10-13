(ns rainbow.math.linear.vector.norm
  "The Euclidean vector norm over signed-rational vectors, built from the inner
  product and the perfect-square root witness:

      norm-squared v = <v, v>
      is-norm v n    <=>  n * n ~ <v, v>

  The squared norm is exact (a dot product); the norm itself is exact only on
  perfect-square instances (a witness n with n*n ~ norm-squared). Worked: [3,4]
  has squared norm 25 and norm 5. This unblocks gradient-norm stopping criteria,
  vector normalization, and cosine similarity.

  Requires `signed/multiply` and `vector/dot` in the environment."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- signed-multiply [l r]
  (function/app (function/const* 'signed/multiply []) l r))
(defn- vector-dot [l r]
  (function/app (function/const* 'vector/dot []) l r))
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

(defn- norm-squared [v]
  (function/app (function/const* 'norm/norm-squared []) v))
(defn- is-norm [v n]
  (function/app (function/const* 'norm/is-norm []) v n))

(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

(def norm-squared-spec
  {:name 'norm/norm-squared :kind :definition :universes []
   :type (function/arrow vector-type signed)
   :value (function/lam [['v vector-type]] (vector-dot 'v 'v))})

(def is-norm-spec
  {:name 'norm/is-norm :kind :definition :universes []
   :type (function/arrow vector-type signed 'Prop)
   :value (function/lam [['v vector-type] ['n signed]]
                        (signed-equivalent (signed-multiply 'n 'n)
                                           (norm-squared 'v)))})

(def definition-specs [norm-squared-spec is-norm-spec])

;; Theorems -----------------------------------------------------------------

;; The squared norm of [3,4] is 25.
(def norm-squared-example-spec
  {:name 'norm/norm-squared-example :universes []
   :type (signed-equivalent
          (norm-squared (make-vector (signed-numeral 3) (signed-numeral 4)))
          (signed-numeral 25))
   :value (signed-cross-reflexivity
           (norm-squared (make-vector (signed-numeral 3) (signed-numeral 4)))
           (signed-numeral 25))})

;; 5 is the norm of [3,4] (5*5 = 25 = 3^2 + 4^2).
(def norm-example-spec
  {:name 'norm/norm-example :universes []
   :type (is-norm (make-vector (signed-numeral 3) (signed-numeral 4))
                  (signed-numeral 5))
   :value (signed-cross-reflexivity
           (signed-multiply (signed-numeral 5) (signed-numeral 5))
           (norm-squared (make-vector (signed-numeral 3) (signed-numeral 4))))})

;; A three-dimensional unit direction: 1 is the norm of [1,0,0].
(def unit-norm-example-spec
  {:name 'norm/unit-norm-example :universes []
   :type (is-norm (make-vector (signed-numeral 1) (signed-numeral 0)
                               (signed-numeral 0))
                  (signed-numeral 1))
   :value (signed-cross-reflexivity
           (signed-multiply (signed-numeral 1) (signed-numeral 1))
           (norm-squared (make-vector (signed-numeral 1) (signed-numeral 0)
                                      (signed-numeral 0))))})

(def theorem-specs
  [norm-squared-example-spec norm-example-spec unit-norm-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :vector-norm (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.norm))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
