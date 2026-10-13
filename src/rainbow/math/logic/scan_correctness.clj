(ns rainbow.math.logic.scan-correctness
  "GENERAL (abstract-element) correctness theorems for the prefix-sum scan: for
  arbitrary list elements a, b, c the running totals are exactly the prefix sums,

      cumulative-sum [a]       = [a]
      cumulative-sum [a, b]    = [a, a + b]
      cumulative-sum [a, b, c] = [a, a + b, a + b + c].

  Unlike the numeric worked examples in prefix-sum, these are universally
  quantified over the elements (proved for ALL a, b, c), so they certify the
  scan's meaning, not just specific outputs. Each holds by reflexivity: the
  higher-order scan fold unfolds and the leading accumulator offset 0 + a reduces
  definitionally to a (nat-add recurses on its left argument), leaving exactly the
  prefix-sum list.

  Requires prefix-sum/cumulative-sum, algebra/nat-add, data/cons/nil (D63
  checkpoint plus the prefix-sum module)."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.prefix-sum :as prefix-sum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def list-nat
  (function/app (function/const* 'data/List [type-level]) nat))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))
(def nil-nat
  (function/app (function/const* 'data/nil [type-level]) nat))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cumulative-sum [xs]
  (function/app (function/const* 'prefix-sum/cumulative-sum []) xs))
(defn- nat-list [& elements]
  (reduce (fn [tail element] (cons-nat element tail)) nil-nat (reverse elements)))

;; Theorems -----------------------------------------------------------------

;; For all a: cumulative-sum [a] = [a].
(def singleton-correct-spec
  {:name 'scan-correctness/singleton :universes []
   :type (function/forall
          [['a nat]]
          (equality list-nat (cumulative-sum (nat-list 'a)) (nat-list 'a)))
   :value (function/lam
           [['a nat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         list-nat (cumulative-sum (nat-list 'a))))})

;; For all a b: cumulative-sum [a, b] = [a, a + b].
(def pair-correct-spec
  {:name 'scan-correctness/pair :universes []
   :type (function/forall
          [['a nat] ['b nat]]
          (equality list-nat
                    (cumulative-sum (nat-list 'a 'b))
                    (nat-list 'a (add 'a 'b))))
   :value (function/lam
           [['a nat] ['b nat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         list-nat (cumulative-sum (nat-list 'a 'b))))})

;; For all a b c: cumulative-sum [a, b, c] = [a, a + b, (a + b) + c].
(def triple-correct-spec
  {:name 'scan-correctness/triple :universes []
   :type (function/forall
          [['a nat] ['b nat] ['c nat]]
          (equality list-nat
                    (cumulative-sum (nat-list 'a 'b 'c))
                    (nat-list 'a (add 'a 'b) (add (add 'a 'b) 'c))))
   :value (function/lam
           [['a nat] ['b nat] ['c nat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         list-nat (cumulative-sum (nat-list 'a 'b 'c))))})

(def theorem-specs
  [singleton-correct-spec pair-correct-spec triple-correct-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.prefix-sum])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :scan-correctness theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.logic.scan-correctness))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
