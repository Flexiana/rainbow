(ns rainbow.math.nat.power
  "Natural-number exponentiation base^exp, defined by recursion on the exponent:

      power b 0        = 1
      power b (succ e) = b * (power b e).

  This is the growth primitive missing from the arithmetic core: it is what the
  full-factorial design size n^k, sparse-sampling node counts (branching^depth),
  and -- crucially -- the geometric-convergence modulus need. The archimedean
  bound d0 <= eps * 2^n that drives the contraction distance below any threshold
  is stated in terms of 2^n = power 2 n, so this definition and its
  monotonicity are the foundation for the general forall-epsilon convergence
  theorem.

  Requires nat and nat/multiply (carried by the D63 checkpoint)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def one (function/app (function/const* 'data/succ []) (function/const* 'data/zero [])))
(def successor (function/const* 'data/succ []))

(defn- multiply [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- succ [n] (function/app successor n))

(defn- power [base exp]
  (function/app (function/const* 'nat/power []) base exp))

;; Definitions --------------------------------------------------------------

;; power base exp = base^exp, by recursion on the exponent.
(def power-spec
  {:name 'nat/power :kind :definition :universes []
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['base nat] ['exp nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nat)
     one
     (function/lam [['predecessor nat] ['previous nat]]
                   (multiply 'base 'previous))
     'exp))})

(def definition-specs [power-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; The recurrence: base^(succ e) = base * base^e  (Nat.rec computation rule).
(def power-step-unfold-spec
  {:name 'nat/power-step-unfold :universes []
   :type (function/forall
          [['base nat] ['exp nat]]
          (equality nat
                    (power 'base (succ 'exp))
                    (multiply 'base (power 'base 'exp))))
   :value (function/lam
           [['base nat] ['exp nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (power 'base (succ 'exp))))})

;; base^0 = 1 for every base.
(def power-zero-spec
  {:name 'nat/power-zero :universes []
   :type (function/forall [['base nat]]
                          (equality nat (power 'base (data-nat 0)) one))
   :value (function/lam
           [['base nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (power 'base (data-nat 0))))})

;; 2^3 = 8.
(def two-cubed-spec
  {:name 'nat/power-two-cubed :universes []
   :type (equality nat (power (data-nat 2) (data-nat 3)) (data-nat 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (power (data-nat 2) (data-nat 3)))})

;; 3^2 = 9.
(def three-squared-spec
  {:name 'nat/power-three-squared :universes []
   :type (equality nat (power (data-nat 3) (data-nat 2)) (data-nat 9))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (power (data-nat 3) (data-nat 2)))})

;; 2^0 = 1  (a concrete base case witness).
(def two-to-zero-spec
  {:name 'nat/power-two-to-zero :universes []
   :type (equality nat (power (data-nat 2) (data-nat 0)) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (power (data-nat 2) (data-nat 0)))})

(def theorem-specs
  [power-step-unfold-spec power-zero-spec two-cubed-spec
   three-squared-spec two-to-zero-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nat-power
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
