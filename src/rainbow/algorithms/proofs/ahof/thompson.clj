(ns rainbow.algorithms.proofs.ahof.thompson
  "AHoF Thompson Sampling (posterior sampling) for multi-armed bandits: instead of
  an explicit exploration bonus, draw one sample from each arm's posterior over
  its mean reward and pull the arm with the largest sample. Arms with uncertain
  posteriors are explored automatically (their samples vary widely), while the
  best-known arm is exploited most often. Given the per-arm posterior samples,
  the selected arm is the argmax:

      thompson-select samples = argmax_a samples(a)

  over exact-rational samples (returning the selected arm index). Proved native
  and axiom-free: the selection is exactly the proved argmax-index fold; a worked
  selection; and the certificate that the selected arm's sample is at least each
  other arm's sample (native nnrat/at-most), so posterior sampling pulls the
  currently-most-promising arm. The posterior model and the sampler are
  executable; what is proved is the argmax arm selection over the samples.

  Requires argmax-index/argmax-index, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.thompson`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- thompson-select [samples]
  (function/app (function/const* 'thompson/select []) samples))
(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; thompson-select samples = argmax_a samples(a)
(def select-spec
  {:name 'thompson/select :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['samples list-nnrat]] (argmax-index-app 'samples))})

(def definition-specs [select-spec])

;; Theorems -----------------------------------------------------------------

(def samples (nnrat-list (whole 5) (whole 8) (whole 4)))

;; Posterior samples [5,8,4]: arm 1 has the largest sample -> pull arm 1.
(def selects-largest-sample-spec
  {:name 'thompson/selects-largest-sample :universes []
   :type (equality nat (thompson-select samples) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (thompson-select samples))})

;; Certificate: the selected arm's sample (8) is at least every other arm's.
(def selected-dominates-arm-zero-spec
  {:name 'thompson/selected-dominates-arm-zero :universes []
   :type (nnrat-at-most (whole 5) (whole 8))
   :value (at-most-proof (whole 5) (whole 8))})

(def selected-dominates-arm-two-spec
  {:name 'thompson/selected-dominates-arm-two :universes []
   :type (nnrat-at-most (whole 4) (whole 8))
   :value (at-most-proof (whole 4) (whole 8))})

(def theorem-specs
  [selects-largest-sample-spec selected-dominates-arm-zero-spec
   selected-dominates-arm-two-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      argmax-index/extend-environment
      (support/extend-with :ahof-thompson
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
