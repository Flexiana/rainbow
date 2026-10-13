(ns rainbow.algorithms.proofs.fibonacci
  "AHoF Fibonacci numbers -- the linear recurrence behind Fibonacci search (the
  derivative-free line-search that places probes at Fibonacci ratios) and a
  canonical dynamic-programming example. Computed in one pass by recursion on n
  carrying the adjacent pair (fib n, fib (n+1)):

      fib-pair 0        = (0, 1)
      fib-pair (succ n) = (snd p, fst p + snd p)   where p = fib-pair n
      fib n             = fst (fib-pair n)

  so fib n is produced in linear time with exact naturals (no double recursion,
  no memo table). Proved native and axiom-free: the pair carries adjacent
  Fibonacci numbers, and worked values reduce by reflexivity (fib 0 = 0,
  fib 1 = 1, fib 7 = 13). The Fibonacci-ratio probe placement of the search is an
  executable concern; what is proved here is the recurrence and worked values.

  Requires nat, nat addition (algebra/nat-add), and the product type
  (data/Product, data/pair, product/first, product/second) -- all in D63.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.fibonacci`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def pair-type
  (function/app (function/const* 'data/Product [type-level type-level]) nat nat))
(def zero (function/const* 'data/zero []))
(def one (function/app (function/const* 'data/succ []) zero))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- make-pair [a b]
  (function/app (function/const* 'data/pair [type-level type-level])
                nat nat a b))
(defn- first-of [p]
  (function/app (function/const* 'product/first [type-level type-level])
                nat nat p))
(defn- second-of [p]
  (function/app (function/const* 'product/second [type-level type-level])
                nat nat p))
(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- fib-pair [n]
  (function/app (function/const* 'fibonacci/pair []) n))
(defn- fib [n]
  (function/app (function/const* 'fibonacci/fib []) n))

;; Definitions --------------------------------------------------------------

;; fib-pair n = (fib n, fib (n+1)), by recursion on n.
(def pair-spec
  {:name 'fibonacci/pair :kind :definition :universes []
   :type (function/arrow nat pair-type)
   :value
   (function/lam
    [['n nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] pair-type)
     (make-pair zero one)
     (function/lam [['predecessor nat] ['previous pair-type]]
                   (make-pair (second-of 'previous)
                              (add (first-of 'previous) (second-of 'previous))))
     'n))})

;; fib n = fst (fib-pair n)
(def fib-spec
  {:name 'fibonacci/fib :kind :definition :universes []
   :type (function/arrow nat nat)
   :value (function/lam [['n nat]] (first-of (fib-pair 'n)))})

(def definition-specs [pair-spec fib-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; The pair advances: fib-pair (succ n) = (snd, fst + snd) of fib-pair n.
(def pair-step-unfold-spec
  {:name 'fibonacci/pair-step-unfold :universes []
   :type (function/forall
          [['n nat]]
          (equality pair-type
                    (fib-pair (succ 'n))
                    (make-pair (second-of (fib-pair 'n))
                               (add (first-of (fib-pair 'n))
                                    (second-of (fib-pair 'n))))))
   :value (function/lam
           [['n nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            pair-type (fib-pair (succ 'n))))})

;; fib 0 = 0.
(def fib-zero-spec
  {:name 'fibonacci/fib-zero :universes []
   :type (equality nat (fib (data-nat 0)) (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fib (data-nat 0)))})

;; fib 1 = 1.
(def fib-one-spec
  {:name 'fibonacci/fib-one :universes []
   :type (equality nat (fib (data-nat 1)) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fib (data-nat 1)))})

;; fib 7 = 13.
(def fib-seven-spec
  {:name 'fibonacci/fib-seven :universes []
   :type (equality nat (fib (data-nat 7)) (data-nat 13))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (fib (data-nat 7)))})

(def theorem-specs
  [pair-step-unfold-spec fib-zero-spec fib-one-spec fib-seven-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :fibonacci (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.fibonacci))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
