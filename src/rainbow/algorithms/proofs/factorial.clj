(ns rainbow.algorithms.proofs.factorial
  "AHoF factorial n! -- the permutation count underlying combinatorial design
  sizes, permutation-based search spaces, and Bayesian model-structure counts.
  Defined by recursion on n, multiplying by the current index at each step:

      fact 0        = 1
      fact (succ n) = (succ n) * fact n.

  Exact naturals, so the count is proved data. Proved native and axiom-free: the
  step recurrence (Nat.rec computation rule, which reads the predecessor to form
  the multiplier), and worked values (0! = 1, 4! = 24, 5! = 120). The
  enumeration of the permutations themselves is an executable concern; what is
  proved here is the factorial recurrence and its worked counts.

  Requires nat and nat/multiply (carried by the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.factorial`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def one (function/app (function/const* 'data/succ []) (function/const* 'data/zero [])))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- multiply [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- fact [n] (function/app (function/const* 'factorial/fact []) n))

;; Definitions --------------------------------------------------------------

;; fact 0 = 1 ; fact (succ n) = (succ n) * fact n
(def fact-spec
  {:name 'factorial/fact :kind :definition :universes []
   :type (function/arrow nat nat)
   :value
   (function/lam
    [['n nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nat)
     one
     (function/lam [['predecessor nat] ['previous nat]]
                   (multiply (succ 'predecessor) 'previous))
     'n))})

(def definition-specs [fact-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; The recurrence: fact (succ n) = (succ n) * fact n  (Nat.rec computation rule).
(def fact-step-unfold-spec
  {:name 'factorial/fact-step-unfold :universes []
   :type (function/forall
          [['n nat]]
          (equality nat (fact (succ 'n)) (multiply (succ 'n) (fact 'n))))
   :value (function/lam
           [['n nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (fact (succ 'n))))})

;; 0! = 1.
(def fact-zero-spec
  {:name 'factorial/fact-zero :universes []
   :type (equality nat (fact (data-nat 0)) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fact (data-nat 0)))})

;; 4! = 24.
(def fact-four-spec
  {:name 'factorial/fact-four :universes []
   :type (equality nat (fact (data-nat 4)) (data-nat 24))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fact (data-nat 4)))})

;; 5! = 120.
(def fact-five-spec
  {:name 'factorial/fact-five :universes []
   :type (equality nat (fact (data-nat 5)) (data-nat 120))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fact (data-nat 5)))})

(def theorem-specs
  [fact-step-unfold-spec fact-zero-spec fact-four-spec fact-five-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :factorial (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.factorial))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
