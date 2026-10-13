(ns rainbow.math.logic.scan-length
  "A GENERAL (for-all-inputs) correctness theorem about the prefix-sum scan:
  scanning a list preserves its length,

      length (cumulative-sum xs) = length xs    for every list xs.

  Unlike the worked examples in prefix-sum (which check specific lists), this is
  proved by induction over ALL lists, with the induction hypothesis generalized
  over the running accumulator -- the essential move for reasoning about the
  higher-order scan fold (whose motive is nat -> list nat). It upgrades the scan
  from 'computes the right answer on examples' to 'proved structurally correct',
  the same jump the convergence capstone made for the geometric sequence.

  Requires prefix-sum/scan-from, algebra/nat-add, data/List.rec,
  equality/reflexive, equality/congruent-function (all in the D63 checkpoint
  plus the prefix-sum module)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.prefix-sum :as prefix-sum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
;; prefix-sum/scan-from operates on List nat (running natural totals), so the
;; length invariant is stated over List nat.
(def list-nat
  (function/app (function/const* 'data/List [type-level]) nat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))
(def nil-nat
  (function/app (function/const* 'data/nil [type-level]) nat))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- scan-from [xs]
  (function/app (function/const* 'prefix-sum/scan-from []) xs))
(defn- ps-length [xs]
  (function/app (function/const* 'scan-length/length []) xs))

;; Definitions --------------------------------------------------------------

;; length xs = fold (+1) 0 xs (a self-contained List.rec into nat)
(def length-spec
  {:name 'scan-length/length :kind :definition :universes []
   :type (function/arrow list-nat nat)
   :value
   (function/lam
    [['xs list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] nat)
     zero
     (function/lam [['head nat] ['tail list-nat] ['ih nat]] (succ 'ih))
     'xs))})

(def definition-specs [length-spec])

;; Theorems -----------------------------------------------------------------

;; General lemma: for every list and every accumulator, scanning preserves
;; length. The motive is a Pi over the accumulator, so the induction hypothesis
;; is available at the shifted accumulator (acc + head).
(def scan-from-preserves-length-spec
  {:name 'scan-length/scan-from-preserves-length :universes []
   :type (function/forall
          [['xs list-nat]]
          (function/forall
           [['acc nat]]
           (equality nat (ps-length (function/app (scan-from 'xs) 'acc))
                     (ps-length 'xs))))
   :value
   (function/lam
    [['xs list-nat]]
    (function/app
    (function/const* 'data/List.rec [type-level zero-level])
    nat
    ;; motive: lambda xs. forall acc. length(scan-from xs acc) = length xs
    (function/lam
     [['xs list-nat]]
     (function/forall
      [['acc nat]]
      (equality nat (ps-length (function/app (scan-from 'xs) 'acc))
                (ps-length 'xs))))
    ;; base (nil): scan-from nil acc reduces to nil, both lengths are 0
    (function/lam
     [['acc nat]]
     (function/app (function/const* 'equality/reflexive [type-level])
                   nat (ps-length (function/app (scan-from nil-nat) 'acc))))
    ;; step (cons head tail): length(scan-from (h::t) acc)
    ;;   = succ(length(scan-from t (acc+h))) = succ(length t) = length(h::t)
    (function/lam
     [['head nat] ['tail list-nat]
      ['ih (function/forall
            [['acc nat]]
            (equality nat (ps-length (function/app (scan-from 'tail) 'acc))
                      (ps-length 'tail)))]]
     (function/lam
      [['acc nat]]
      (function/app
       (function/const* 'equality/congruent-function [type-level type-level])
       nat nat
       (function/lam [['n nat]] (succ 'n))
       (ps-length (function/app (scan-from 'tail) (add 'acc 'head)))
       (ps-length 'tail)
       (function/app 'ih (add 'acc 'head)))))
    'xs))})

;; The headline theorem: cumulative-sum preserves length (accumulator = 0).
(def cumulative-sum-preserves-length-spec
  {:name 'scan-length/cumulative-sum-preserves-length :universes []
   :type (function/forall
          [['xs list-nat]]
          (equality nat
                    (ps-length
                     (function/app (function/const* 'prefix-sum/cumulative-sum [])
                                   'xs))
                    (ps-length 'xs)))
   :value
   (function/lam
    [['xs list-nat]]
    (function/app
     (function/const* 'scan-length/scan-from-preserves-length [])
     'xs zero))})

(def theorem-specs
  [scan-from-preserves-length-spec cumulative-sum-preserves-length-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      prefix-sum/extend-environment
      (support/extend-with :scan-length
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
