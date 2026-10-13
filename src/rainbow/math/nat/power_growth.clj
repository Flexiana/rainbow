(ns rainbow.math.nat.power-growth
  "Growth lemmas for nat exponentiation, on the road to the geometric-convergence
  modulus. The first is positivity of the powers of two:

      1 <= 2^n     for every n,

  proved by induction on n. The base case 2^0 = 1 is reflexive; the step uses
  that 2^(n+1) = 2 * 2^n reduces (through nat/multiply) to 2^n + (2^n + 0), so
  2^n <= 2^(n+1) by nat/le-add-right, and transitivity with the induction
  hypothesis 1 <= 2^n gives 1 <= 2^(n+1). Positivity is the first ingredient of
  the archimedean bound d0 <= eps * 2^n that completes the forall-epsilon
  convergence theorem.

  Requires nat/power, nat/at-most(-reflexive,-transitive), nat/le-add-right,
  algebra/nat-add (d63 checkpoint + nat-add-order)."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def one (function/app (function/const* 'data/succ []) (function/const* 'data/zero [])))
(def successor (function/const* 'data/succ []))
(def zero (function/const* 'data/zero []))

(defn- succ [n] (function/app successor n))
(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- power [base exp] (function/app (function/const* 'nat/power []) base exp))
(defn- at-most [l r] (function/app (function/const* 'nat/at-most []) l r))
(defn- at-most-reflexive [v]
  (function/app (function/const* 'nat/at-most-reflexive []) v))
(defn- at-most-transitive [l m r first second]
  (function/app (function/const* 'nat/at-most-transitive []) l m r first second))
(defn- le-add-right [x y]
  (function/app (function/const* 'nat/le-add-right []) x y))
(defn- at-most-successor [v]
  (function/app (function/const* 'nat/at-most-successor []) v))
(defn- add-monotone [left-a right-a left-b right-b ordered-a ordered-b]
  (function/app (function/const* 'nat/add-monotone [])
                left-a right-a left-b right-b ordered-a ordered-b))
(defn- power-two-at-least-one [n]
  (function/app (function/const* 'nat/power-two-at-least-one []) n))
(defn- nat-add-zero-right [x]
  (function/app (function/const* 'algebra/nat-add-zero-right []) x))
(defn- congruent [f x y h]
  (function/app (function/const* 'equality/congruent-function
                                 [type-level type-level])
                nat nat f x y h))
(defn- symmetric [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- substitute [x y h motive px]
  (function/app (function/const* 'equality/substitution [type-level])
                nat x y h motive px))

(defn- mul [a b] (function/app (function/const* 'nat/multiply []) a b))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

(def two (data-nat 2))
(def zero-term (function/const* 'data/zero []))

;; X <= (succ f) * X : a value is at most any positive multiple of itself.
;; (succ f)*X reduces to X + f*X, so this is nat/le-add-right.
(def le-multiply-succ-spec
  {:name 'nat/le-multiply-succ :universes []
   :type (function/forall [['f nat] ['x nat]]
                          (at-most 'x (mul (succ 'f) 'x)))
   :value (function/lam [['f nat] ['x nat]]
                        (le-add-right 'x (mul 'f 'x)))})

;; 1 <= 2^n for every n.
(def power-two-at-least-one-spec
  {:name 'nat/power-two-at-least-one :universes []
   :type (function/forall [['n nat]] (at-most one (power two 'n)))
   :value
   (function/lam
    [['n nat]]
    (let [motive (function/lam [['m nat]] (at-most one (power two 'm)))
          base (at-most-reflexive one)                ; 1 <= 2^0 = 1
          step (function/lam
                [['m nat] ['ih (function/app motive 'm)]]
                ;; 2^m <= 2^(m+1) = 2^m + (2^m + 0)  by le-add-right;
                ;; transitivity with ih (1 <= 2^m) gives 1 <= 2^(m+1).
                (at-most-transitive
                 one (power two 'm) (power two (succ 'm))
                 'ih
                 (le-add-right (power two 'm)
                               (add (power two 'm) zero))))]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive base step 'n)))})

;; n <= 2^n for every n -- the powers of two dominate their exponent, so 2^n
;; grows without bound. By induction on n: base 0 <= 2^0 = 1 is at-most-successor
;; on 0; the step derives succ n <= 2^(n+1) from add-monotone applied to
;; positivity (1 <= 2^n) and the hypothesis (n <= 2^n): since add 1 n reduces to
;; succ n and 2^(n+1) = 2*2^n reduces to 2^n + (2^n + 0), monotone addition gives
;; succ n <= 2^n + 2^n, and the trailing + 0 is rewritten in by
;; nat-add-zero-right.
(def at-most-power-two-spec
  {:name 'nat/at-most-power-two :universes []
   :type (function/forall [['n nat]] (at-most 'n (power two 'n)))
   :value
   (function/lam
    [['n nat]]
    (let [motive (function/lam [['m nat]] (at-most 'm (power two 'm)))
          base (at-most-successor (function/const* 'data/zero []))
          step (function/lam
                [['m nat] ['ih (function/app motive 'm)]]
                (let [pm (power two 'm)
                      ;; succ m <= 2^m + 2^m   (add 1 m reduces to succ m)
                      monotone (add-monotone one pm 'm pm
                                             (power-two-at-least-one 'm) 'ih)
                      ;; 2^m + 2^m = 2^m + (2^m + 0) = 2^(m+1)
                      rewrite (congruent
                               (function/lam [['v nat]] (add pm 'v))
                               pm (add pm zero-term)
                               (symmetric (add pm zero-term) pm
                                          (nat-add-zero-right pm)))]
                  (substitute (add pm pm) (add pm (add pm zero-term))
                              rewrite
                              (function/lam [['r nat]] (at-most (succ 'm) 'r))
                              monotone)))]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive base step 'n)))})

(def definition-specs [])
(def theorem-specs
  [power-two-at-least-one-spec at-most-power-two-spec le-multiply-succ-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nat-power-growth theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.power-growth))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
