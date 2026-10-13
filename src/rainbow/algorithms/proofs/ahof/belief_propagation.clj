(ns rainbow.algorithms.proofs.ahof.belief-propagation
  "AHoF D4 Sum-Product (Belief Propagation): approximate marginal inference by
  passing messages on the factor graph until convergence. A variable node's
  outgoing message is the pointwise PRODUCT of the messages it receives from its
  other neighbors (the belief is the product of all incoming messages):

      combine-messages m1 m2 = m1 * m2

  over exact nonnegative rationals (two incoming messages; the general node folds
  the product over all neighbors). Proved native and axiom-free: the combination
  unfolds to m1 * m2 for all messages m1 and m2, and two worked instances, 3 * 4 =
  12 and a zero message 0 * 7 = 0, that reduce by reflexivity. The factor-node
  sum-product messages and the message schedule are executable concerns; what is
  proved here is the variable-node message product.

  Requires nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.belief-propagation`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- combine-messages [m1 m2]
  (function/app (function/const* 'belief-propagation/combine-messages []) m1 m2))

;; Definitions --------------------------------------------------------------

;; combine-messages m1 m2 = m1 * m2
(def combine-messages-spec
  {:name 'belief-propagation/combine-messages :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['m1 nnrat] ['m2 nnrat]]
                        (nnrat-multiply 'm1 'm2))})

(def definition-specs [combine-messages-spec])

;; Theorems -----------------------------------------------------------------

(def combine-messages-unfold-spec
  {:name 'belief-propagation/combine-messages-unfold :universes []
   :type (function/forall
          [['m1 nnrat] ['m2 nnrat]]
          (equality nnrat
                    (combine-messages 'm1 'm2)
                    (nnrat-multiply 'm1 'm2)))
   :value (function/lam [['m1 nnrat] ['m2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (combine-messages 'm1 'm2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def rational-zero (function/const* 'nnrat/zero []))

;; Worked belief: incoming messages 3 and 4 combine to 12.
(def combine-messages-example-spec
  {:name 'belief-propagation/combine-messages-example :universes []
   :type (equality nnrat (combine-messages (whole 3) (whole 4)) (whole 12))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (combine-messages (whole 3) (whole 4)))})

;; Worked: a zero message against 7 gives a zero belief (0 * 7 = 0).
(def zero-message-annihilates-spec
  {:name 'belief-propagation/zero-message-annihilates :universes []
   :type (equality nnrat (combine-messages rational-zero (whole 7)) rational-zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (combine-messages rational-zero (whole 7)))})

(def theorem-specs
  [combine-messages-unfold-spec combine-messages-example-spec
   zero-message-annihilates-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-belief-propagation
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
