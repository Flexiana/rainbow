(ns rainbow.algorithms.proofs.ahof.set-cover
  "AHoF Set Cover (greedy approximation): given a universe of elements and a
  collection of subsets, choose the fewest subsets whose union is the whole
  universe. The greedy algorithm -- whose approximation ratio is the harmonic
  number H_n = 1 + 1/2 + ... + 1/n <= 1 + ln(n) for n elements (Chvatal 1979),
  logarithmic and asymptotically best possible for this NP-hard problem --
  repeatedly picks the subset that covers the most still-UNCOVERED elements.
  Given each candidate subset's count of newly-covered elements, the pick is the
  argmax:

      greedy-pick coverage = argmax_s coverage(s)

  over exact-rational (integer) coverage counts (returning the chosen subset
  index). Proved native and axiom-free: the greedy pick is defined as the
  argmax-index fold over coverage counts; a worked pick on counts [2,5,3] selects
  subset 1; and the worked certificates 2 <= 5 and 3 <= 5 as native
  nnrat/at-most. The set/element bookkeeping and coverage recomputation are
  executable; what is proved is the maximum-coverage pick at this instance. The
  H_n <= 1 + ln(n) approximation bound of greedy set cover is classical and not
  proved here.

  Requires argmax-index/argmax-index, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.set-cover`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- greedy-pick [coverage]
  (function/app (function/const* 'set-cover/greedy-pick []) coverage))
(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; greedy-pick coverage = argmax_s coverage(s)
(def greedy-pick-spec
  {:name 'set-cover/greedy-pick :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['coverage list-nnrat]] (argmax-index-app 'coverage))})

(def definition-specs [greedy-pick-spec])

;; Theorems -----------------------------------------------------------------

(def coverage (nnrat-list (whole 2) (whole 5) (whole 3)))

;; Coverage counts [2,5,3]: subset 1 covers the most new elements -> pick it.
(def picks-max-coverage-spec
  {:name 'set-cover/picks-max-coverage :universes []
   :type (equality nat (greedy-pick coverage) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (greedy-pick coverage))})

;; Worked certificate: subset 0 count 2 <= chosen count 5.
(def chosen-covers-most-vs-zero-spec
  {:name 'set-cover/chosen-covers-most-vs-zero :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; Worked certificate: subset 2 count 3 <= chosen count 5.
(def chosen-covers-most-vs-two-spec
  {:name 'set-cover/chosen-covers-most-vs-two :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

(def theorem-specs
  [picks-max-coverage-spec chosen-covers-most-vs-zero-spec
   chosen-covers-most-vs-two-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.argmax-index])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-set-cover (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.set-cover))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
