(ns rainbow.algorithms.proofs.ahof.log-loss
  "AHoF Cross-Entropy / Log Loss: the standard loss for probabilistic
  classification and the maximum-likelihood objective for logistic regression and
  softmax networks. The per-example loss for the true class is -log(p_true): zero
  when the model is certain and correct, growing without bound as the predicted
  true-class probability goes to zero, so confident wrong predictions are strongly
  penalized. Because -log is strictly decreasing, a HIGHER true-class probability
  gives a LOWER loss; comparing two predictions' losses reduces to comparing their
  true-class probabilities:

      lower-loss? p-confident p-unsure = decide (p-unsure <= p-confident)

  (the more-confident correct prediction has the lower loss), over exact-rational
  probabilities. Proved native and axiom-free, as worked instances: the test says
  true for probability 3/4 against 1/4; the worked certificate 1/4 <= 3/4 (native
  nnrat/at-most); and the test says false for 1/4 against 3/4. That -log is
  strictly decreasing, so the test matches the loss order for all inputs, is
  classical and not proved here; the logarithm is executable. This is the LOSS
  FUNCTION, distinct from O41's cross-entropy optimization METHOD.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.log-loss`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- lower-loss? [p-confident p-unsure]
  (function/app (function/const* 'log-loss/lower-loss? []) p-confident p-unsure))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def lower-loss-spec
  {:name 'log-loss/lower-loss? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['p-confident nnrat] ['p-unsure nnrat]]
                        (decide-at-most 'p-unsure 'p-confident))})

(def definition-specs [lower-loss-spec])

(def confident-has-lower-loss-spec
  {:name 'log-loss/confident-has-lower-loss :universes []
   :type (equality bool (lower-loss? (fraction 3 3) (fraction 1 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (lower-loss? (fraction 3 3) (fraction 1 3)))})

(def lower-loss-more-probable-spec
  {:name 'log-loss/lower-loss-more-probable :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 3 3))
   :value (at-most-proof (fraction 1 3) (fraction 3 3))})

(def unsure-not-lower-loss-spec
  {:name 'log-loss/unsure-not-lower-loss :universes []
   :type (equality bool (lower-loss? (fraction 1 3) (fraction 3 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (lower-loss? (fraction 1 3) (fraction 3 3)))})

(def theorem-specs
  [confident-has-lower-loss-spec lower-loss-more-probable-spec
   unsure-not-lower-loss-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-log-loss (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.log-loss))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
