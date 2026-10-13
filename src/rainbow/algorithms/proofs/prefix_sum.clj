(ns rainbow.algorithms.proofs.prefix-sum
  "Cumulative sum (prefix-sum / scan): the running totals of a list,

      cumulative-sum [x0, x1, x2, ...] = [x0, x0+x1, x0+x1+x2, ...].

  This is the scan primitive behind CDF construction for inverse-transform
  sampling (AHoF D5), roulette-wheel selection (genetic algorithms), and
  cumulative-reward / return-to-date accounting. It is proved as a native
  higher-order fold: List.rec whose motive is the function type (nat -> list nat),
  threading the running accumulator so that each output entry is the accumulator
  plus the current element. Proved axiom-free: the scan, its cons recurrence, and
  a worked running-total, all reducing by reflexivity.

  Requires nat, algebra/nat-add, and data/List.rec (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.prefix-sum`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def list-nat (function/app (function/const* 'data/List [type-level]) nat))
(def acc-fn (function/arrow nat list-nat))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))
(def nil-nat (function/app (function/const* 'data/nil [type-level]) nat))

(defn- cumulative-sum [xs]
  (function/app (function/const* 'prefix-sum/cumulative-sum []) xs))
;; the higher-order worker: scan-from xs acc = prefixes of xs offset by acc
(defn- scan-from [xs]
  (function/app (function/const* 'prefix-sum/scan-from []) xs))

;; Definitions --------------------------------------------------------------

;; scan-from xs = \acc. running totals of xs starting from acc
;; (List.rec with the function-typed motive nat -> list nat)
(def scan-from-spec
  {:name 'prefix-sum/scan-from :kind :definition :universes []
   :type (function/arrow list-nat acc-fn)
   :value
   (function/lam
    [['xs list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] acc-fn)
     (function/lam [['acc nat]] nil-nat)
     (function/lam [['head nat] ['tail list-nat] ['rest acc-fn]]
                   (function/lam [['acc nat]]
                                 (cons-nat (add 'acc 'head)
                                           (function/app 'rest
                                                         (add 'acc 'head)))))
     'xs))})

;; cumulative-sum xs = scan-from xs 0
(def cumulative-sum-spec
  {:name 'prefix-sum/cumulative-sum :kind :definition :universes []
   :type (function/arrow list-nat list-nat)
   :value (function/lam [['xs list-nat]]
                        (function/app (scan-from 'xs) zero))})

(def definition-specs [scan-from-spec cumulative-sum-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nat-list [& elements]
  (reduce (fn [tail element] (cons-nat element tail)) nil-nat
          (reverse elements)))

;; The scan recurrence: scanning (x :: rest) from acc emits (acc + x) then scans
;; the rest from (acc + x).
(def scan-cons-spec
  {:name 'prefix-sum/scan-cons :universes []
   :type (function/forall
          [['acc nat] ['head nat] ['tail list-nat]]
          (equality list-nat
                    (function/app (scan-from (cons-nat 'head 'tail)) 'acc)
                    (cons-nat (add 'acc 'head)
                              (function/app (scan-from 'tail)
                                            (add 'acc 'head)))))
   :value (function/lam
           [['acc nat] ['head nat] ['tail list-nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            list-nat
            (function/app (scan-from (cons-nat 'head 'tail)) 'acc)))})

;; Worked running total: cumulative-sum [1,2,3] = [1,3,6].
(def cumulative-sum-example-spec
  {:name 'prefix-sum/cumulative-sum-example :universes []
   :type (equality list-nat
                   (cumulative-sum (nat-list (data-nat 1) (data-nat 2)
                                             (data-nat 3)))
                   (nat-list (data-nat 1) (data-nat 3) (data-nat 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        list-nat
                        (cumulative-sum (nat-list (data-nat 1) (data-nat 2)
                                                  (data-nat 3))))})

;; The empty list has an empty running total.
(def cumulative-sum-empty-spec
  {:name 'prefix-sum/cumulative-sum-empty :universes []
   :type (equality list-nat (cumulative-sum (nat-list)) nil-nat)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        list-nat (cumulative-sum (nat-list)))})

(def theorem-specs
  [scan-cons-spec cumulative-sum-example-spec cumulative-sum-empty-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :prefix-sum
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
