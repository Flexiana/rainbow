(ns rainbow.algorithms.proofs.order-statistic
  "AHoF empirical rank / order statistic: the count of sample values that fall at
  or below a threshold,

      count-at-most t xs = |{ x in xs : x <= t }|,

  the unnormalized empirical CDF at t that underlies quantile estimation, rank
  statistics, and Monte-Carlo hit counting. It is a fold over the sample list
  that increments a natural counter exactly when the decidable rational
  comparison x <= t holds:

      count-at-most t []          = 0
      count-at-most t (x :: rest) = if (x <= t) then succ (count rest)
                                                 else count rest.

  Exact naturals and the decidable rational order, so the count is proved data.
  The threshold sweep that turns counts into a full empirical CDF or quantile is
  an executable concern; what is proved here is the counting fold, its
  cons recurrence, and worked counts.

  Requires nat, decidable nnrat order (audit/decide-nnrat-at-most), logic/if-data,
  and data/List.rec (all carried by the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.order-statistic`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat (function/app (function/const* 'data/List [type-level]) nnrat))
(def zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-nat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nat (condition decision) decision then-value else-value))

(defn- count-at-most [threshold xs]
  (function/app (function/const* 'order-statistic/count-at-most []) threshold xs))

;; Definitions --------------------------------------------------------------

;; count-at-most t xs = fold (increment when head <= t) 0 xs
(def count-at-most-spec
  {:name 'order-statistic/count-at-most :kind :definition :universes []
   :type (function/arrow nnrat list-nnrat nat)
   :value
   (function/lam
    [['threshold nnrat] ['xs list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nat)
     zero
     (function/lam
      [['head nnrat] ['tail list-nnrat] ['tail-count nat]]
      (if-nat (decide-at-most 'head 'threshold)
              (succ 'tail-count)
              'tail-count))
     'xs))})

(def definition-specs [count-at-most-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- sample-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail))
          (function/app (function/const* 'data/nil [type-level]) nnrat)
          (reverse elements)))

;; The cons recurrence, specialised to a value that passes the threshold:
;; prepending 3 (<= 5) to a sample increments the count.
(def cons-below-increments-spec
  {:name 'order-statistic/cons-below-increments :universes []
   :type (function/forall
          [['xs list-nnrat]]
          (equality nat
                    (count-at-most (whole 5) (cons-nnrat (whole 3) 'xs))
                    (succ (count-at-most (whole 5) 'xs))))
   :value (function/lam
           [['xs list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (count-at-most (whole 5) (cons-nnrat (whole 3) 'xs))))})

;; Prepending 7 (> 5) leaves the count unchanged.
(def cons-above-preserves-spec
  {:name 'order-statistic/cons-above-preserves :universes []
   :type (function/forall
          [['xs list-nnrat]]
          (equality nat
                    (count-at-most (whole 5) (cons-nnrat (whole 7) 'xs))
                    (count-at-most (whole 5) 'xs)))
   :value (function/lam
           [['xs list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (count-at-most (whole 5) (cons-nnrat (whole 7) 'xs))))})

;; Worked: of [3,7,2], two values are at most 5.
(def count-example-spec
  {:name 'order-statistic/count-example :universes []
   :type (equality nat
                   (count-at-most (whole 5)
                                  (sample-list (whole 3) (whole 7) (whole 2)))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (count-at-most (whole 5)
                                       (sample-list (whole 3) (whole 7)
                                                    (whole 2))))})

;; The empty sample has no values below any threshold.
(def count-empty-spec
  {:name 'order-statistic/count-empty :universes []
   :type (equality nat (count-at-most (whole 5) (sample-list)) zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (count-at-most (whole 5) (sample-list)))})

(def theorem-specs
  [cons-below-increments-spec cons-above-preserves-spec
   count-example-spec count-empty-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :order-statistic (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.order-statistic))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
