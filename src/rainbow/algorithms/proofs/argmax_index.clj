(ns rainbow.algorithms.proofs.argmax-index
  "Argmax over a list of nonnegative rationals, returning the INDEX of the
  maximum element (the first index attaining it):

      argmax-index [x0, x1, ...] = the i minimizing (-x_i), ties to the earliest.

  This is the primitive behind greedy policy extraction (pi(s) = argmax_a Q(s,a)),
  action selection in value/policy iteration, and best-arm identification in
  bandits -- wherever you need WHICH option is best, not just its value. It is
  proved as a native HIGHER-ORDER fold: a data/List.rec whose motive is the
  function type (nat -> Product nat nnrat), threading the running index forward
  and carrying the (best-index, best-value) pair; at each element the running
  index wins a tie-or-better against the best of the suffix (via logic/if-data
  over the decision audit/decide-nnrat-at-most). Proved axiom-free: the fold, the
  empty case, and worked argmaxes -- all reducing by reflexivity.

  Requires nnrat, nat, audit/decide-nnrat-at-most, logic/if-data,
  data/Product/pair/product, and data/List.rec (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.argmax-index`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def prod
  (function/app (function/const* 'data/Product [type-level type-level]) nat nnrat))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))
(def index-fn (function/arrow nat prod))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def zero-nnrat (whole 0))

(defn- pair-val [i v]
  (function/app (function/const* 'data/pair [type-level type-level]) nat nnrat i v))
(defn- first-of [p]
  (function/app (function/const* 'product/first [type-level type-level])
                nat nnrat p))
(defn- second-of [p]
  (function/app (function/const* 'product/second [type-level type-level])
                nat nnrat p))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-prod [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                prod (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- argmax-from [xs]
  (function/app (function/const* 'argmax-index/argmax-from []) xs))
(defn- argmax-index [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))

;; Definitions --------------------------------------------------------------

;; argmax-from xs = \i. (best-index, best-value) of xs with indices from i
;; (higher-order List.rec: motive nat -> Product nat nnrat)
(def argmax-from-spec
  {:name 'argmax-index/argmax-from :kind :definition :universes []
   :type (function/arrow list-nnrat index-fn)
   :value
   (function/lam
    [['xs list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] index-fn)
     ;; base (nil) at index i: no element, carry (i, 0)
     (function/lam [['i nat]] (pair-val 'i zero-nnrat))
     ;; step: head at index i wins a tie-or-better against best of the suffix
     (function/lam [['head nnrat] ['tail list-nnrat] ['rest index-fn]]
                   (function/lam [['i nat]]
                                 (if-prod
                                  (decide-at-most
                                   (second-of (function/app 'rest (succ 'i)))
                                   'head)
                                  (pair-val 'i 'head)
                                  (function/app 'rest (succ 'i)))))
     'xs))})

;; argmax-index xs = best index = first component of (argmax-from xs 0)
(def argmax-index-spec
  {:name 'argmax-index/argmax-index :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['xs list-nnrat]]
                        (first-of (function/app (argmax-from 'xs)
                                                (data-nat 0))))})

(def definition-specs [argmax-from-spec argmax-index-spec])

;; Theorems -----------------------------------------------------------------

(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

;; argmax-index [5, 7, 4] = 1 (the maximum 7 is at index 1).
(def argmax-middle-spec
  {:name 'argmax-index/argmax-middle :universes []
   :type (equality nat
                   (argmax-index (nnrat-list (whole 5) (whole 7) (whole 4)))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (argmax-index (nnrat-list (whole 5) (whole 7)
                                                  (whole 4))))})

;; argmax-index [8, 3, 2] = 0 (leading maximum).
(def argmax-first-spec
  {:name 'argmax-index/argmax-first :universes []
   :type (equality nat
                   (argmax-index (nnrat-list (whole 8) (whole 3) (whole 2)))
                   (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (argmax-index (nnrat-list (whole 8) (whole 3)
                                                  (whole 2))))})

;; argmax-index [2, 4, 9] = 2 (trailing maximum).
(def argmax-last-spec
  {:name 'argmax-index/argmax-last :universes []
   :type (equality nat
                   (argmax-index (nnrat-list (whole 2) (whole 4) (whole 9)))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (argmax-index (nnrat-list (whole 2) (whole 4)
                                                  (whole 9))))})

(def theorem-specs [argmax-middle-spec argmax-first-spec argmax-last-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :argmax-index (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.argmax-index))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
