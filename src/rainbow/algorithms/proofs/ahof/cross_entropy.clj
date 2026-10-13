(ns rainbow.algorithms.proofs.ahof.cross-entropy
  "AHoF O41 Cross-Entropy Method: a model-based stochastic optimizer that, each
  iteration, samples a population, keeps the top-scoring ELITE, and refits the
  sampling distribution to the elite. The elite-selection core is the membership
  test -- a sample is elite when its objective value reaches the elite threshold
  (the rho-quantile of the population scores):

      elite? score threshold = decide (threshold <= score)

  over the decidable rational order (maximization convention). Defined: the
  elite test. Proved native and axiom-free, as worked instances: score 7 against
  threshold 5 is elite, score 3 against threshold 5 is not, and the worked
  certificate 5 <= 7 (native nnrat/at-most). Soundness of the elite test for all
  scores, and the method's classical convergence behaviour, are not proved here.
  The population sampling, the quantile threshold computation, and the
  distribution refit are executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most, and
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cross-entropy`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- elite? [score threshold]
  (function/app (function/const* 'cross-entropy/elite? []) score threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; elite? score threshold = decide (threshold <= score)
(def elite-spec
  {:name 'cross-entropy/elite? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['score nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'score))})

(def definition-specs [elite-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A high-scoring sample (score 7 >= threshold 5) is selected as elite.
(def selects-elite-spec
  {:name 'cross-entropy/selects-elite :universes []
   :type (equality bool (elite? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (elite? (whole 7) (whole 5)))})

;; Worked certificate 5 <= 7. Soundness of the elite test for all scores is not
;; proved here.
(def elite-meets-threshold-spec
  {:name 'cross-entropy/elite-meets-threshold :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A low-scoring sample (score 3 < threshold 5) is excluded from the elite.
(def excludes-non-elite-spec
  {:name 'cross-entropy/excludes-non-elite :universes []
   :type (equality bool (elite? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (elite? (whole 3) (whole 5)))})

(def theorem-specs
  [selects-elite-spec elite-meets-threshold-spec excludes-non-elite-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-cross-entropy
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
