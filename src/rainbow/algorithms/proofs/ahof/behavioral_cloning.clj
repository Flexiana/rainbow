(ns rainbow.algorithms.proofs.ahof.behavioral-cloning
  "AHoF D64 Behavioral Cloning (imitation learning): train a policy by supervised
  learning to reproduce an expert's actions, minimizing an imitation loss. The clone
  is accepted on a demonstration when its loss is within a tolerance:

      within-tolerance? loss tolerance = decide (loss <= tolerance).

  A zero loss (perfect match) is within any tolerance; a loss 1/4 within tolerance 1/2
  is accepted; a loss 3/4 exceeding the tolerance is rejected. Proved native and
  axiom-free (decision, perfect and acceptable instances, at-most certificate,
  rejection). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.behavioral-cloning`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

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
(defn- whole [n] (fraction n 0))
(defn- within-tolerance? [loss tolerance]
  (function/app (function/const* 'cloning/within-tolerance? []) loss tolerance))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def within-tolerance-spec
  {:name 'cloning/within-tolerance? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['loss nnrat] ['tolerance nnrat]]
                        (decide-at-most 'loss 'tolerance))})

(def definition-specs [within-tolerance-spec])

(def perfect-match-accepted-spec
  {:name 'cloning/perfect-match-accepted :universes []
   :type (equality bool (within-tolerance? (whole 0) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-tolerance? (whole 0) (fraction 1 1)))})

(def close-clone-accepted-spec
  {:name 'cloning/close-clone-accepted :universes []
   :type (equality bool (within-tolerance? (fraction 1 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-tolerance? (fraction 1 3) (fraction 1 1)))})

(def acceptance-certificate-spec
  {:name 'cloning/acceptance-certificate :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def poor-clone-rejected-spec
  {:name 'cloning/poor-clone-rejected :universes []
   :type (equality bool (within-tolerance? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-tolerance? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [perfect-match-accepted-spec close-clone-accepted-spec
   acceptance-certificate-spec poor-clone-rejected-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-behavioral-cloning (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.behavioral-cloning))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
