(ns rainbow.algorithms.proofs.ahof.hmm-forward
  "AHoF HMM Forward Algorithm: compute the TOTAL likelihood of an observation
  sequence under a Hidden Markov Model by summing over all hidden-state paths --
  the sum-product companion to Viterbi's max-product decoding. The forward
  variable alpha_t(j) accumulates the probability of the observations up to time t
  ending in state j:

      alpha-step a0 t0 a1 t1 emission = (a0*t0 + a1*t1) * emission

  (a two-predecessor step: sum the incoming path masses weighted by transition
  probabilities, then multiply by the emission), over exact-rational
  probabilities. Proved native and axiom-free: the forward-step sum-of-products
  times emission (stated as rational equivalence via the cross-product
  certificate, since the mixed fractions are not in lowest terms); and a
  degenerate step where a single certain predecessor propagates its mass exactly.
  The observation sequence and full recursion are executable; what is proved is the
  forward-step combination.

  Requires nnrat/add, nnrat/multiply, nnrat/equivalent (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hmm-forward`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- nnrat-equivalent [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- numerator-of [v]
  (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator-of [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-multiply [a b]
  (function/app (function/const* 'nat/multiply []) a b))
(defn- equivalent-proof [a b]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (nat-multiply (numerator-of a) (denominator-of b))))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- alpha-step [a0 t0 a1 t1 emission]
  (function/app (function/const* 'hmm-forward/alpha-step []) a0 t0 a1 t1 emission))

;; Definitions --------------------------------------------------------------

;; alpha-step a0 t0 a1 t1 emission = (a0*t0 + a1*t1) * emission
(def alpha-step-spec
  {:name 'hmm-forward/alpha-step :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['a0 nnrat] ['t0 nnrat] ['a1 nnrat] ['t1 nnrat]
                         ['emission nnrat]]
                        (nnrat-multiply
                         (nnrat-add (nnrat-multiply 'a0 't0)
                                    (nnrat-multiply 'a1 't1))
                         'emission))})

(def definition-specs [alpha-step-spec])

;; Theorems -----------------------------------------------------------------

;; Two predecessors each with mass 1/2 and transition 1/2, emission 1:
;; (1/4 + 1/4)*1 = 1/2 (as rational equivalence -- combined fractions not reduced).
(def alpha-step-example-spec
  {:name 'hmm-forward/alpha-step-example :universes []
   :type (nnrat-equivalent
          (alpha-step (fraction 1 1) (fraction 1 1) (fraction 1 1) (fraction 1 1)
                      (whole 1))
          (fraction 1 1))
   :value (equivalent-proof
           (alpha-step (fraction 1 1) (fraction 1 1) (fraction 1 1) (fraction 1 1)
                       (whole 1))
           (fraction 1 1))})

;; A single certain predecessor (mass 1, transition 1, the other transition 0)
;; with emission 1 propagates its mass exactly: (1*1 + 0*0)*1 = 1.
(def certain-predecessor-spec
  {:name 'hmm-forward/certain-predecessor :universes []
   :type (nnrat-equivalent
          (alpha-step (whole 1) (whole 1) (whole 0) (whole 0) (whole 1))
          (whole 1))
   :value (equivalent-proof
           (alpha-step (whole 1) (whole 1) (whole 0) (whole 0) (whole 1))
           (whole 1))})

(def theorem-specs [alpha-step-example-spec certain-predecessor-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-hmm-forward
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
