(ns rainbow.algorithms.proofs.triangular
  "AHoF triangular numbers T(n) = 0 + 1 + ... + n -- the arithmetic-series sum
  that counts pairwise interactions and quantifies the cost of quadratic
  algorithms (all-pairs comparisons, insertion-sort work, full pivoting). Defined
  by recursion on n, adding the current index at each step:

      T 0        = 0
      T (succ n) = (succ n) + T n.

  Exact naturals. Proved native and axiom-free: the step recurrence (Nat.rec
  computation rule) and worked values (T 0 = 0, T 4 = 10, T 5 = 15). The
  Gauss closed form n(n+1)/2 is exercised in the executable; what is proved
  here is the additive recurrence and worked sums.

  Requires nat and nat addition (algebra/nat-add), carried by the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.triangular`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- triangular [n] (function/app (function/const* 'triangular/number []) n))

;; Definitions --------------------------------------------------------------

;; T 0 = 0 ; T (succ n) = (succ n) + T n
(def number-spec
  {:name 'triangular/number :kind :definition :universes []
   :type (function/arrow nat nat)
   :value
   (function/lam
    [['n nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nat)
     zero
     (function/lam [['predecessor nat] ['previous nat]]
                   (add (succ 'predecessor) 'previous))
     'n))})

(def definition-specs [number-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; The recurrence: T (succ n) = (succ n) + T n  (Nat.rec computation rule).
(def step-unfold-spec
  {:name 'triangular/step-unfold :universes []
   :type (function/forall
          [['n nat]]
          (equality nat (triangular (succ 'n)) (add (succ 'n) (triangular 'n))))
   :value (function/lam
           [['n nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (triangular (succ 'n))))})

;; T 0 = 0.
(def number-zero-spec
  {:name 'triangular/number-zero :universes []
   :type (equality nat (triangular (data-nat 0)) (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (triangular (data-nat 0)))})

;; T 4 = 10.
(def number-four-spec
  {:name 'triangular/number-four :universes []
   :type (equality nat (triangular (data-nat 4)) (data-nat 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (triangular (data-nat 4)))})

;; T 5 = 15.
(def number-five-spec
  {:name 'triangular/number-five :universes []
   :type (equality nat (triangular (data-nat 5)) (data-nat 15))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (triangular (data-nat 5)))})

(def theorem-specs
  [step-unfold-spec number-zero-spec number-four-spec number-five-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :triangular (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.triangular))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
