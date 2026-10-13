(ns rainbow.algorithms.proofs.ahof.decision-tree
  "AHoF D-family Decision Tree learning (greedy top-down induction): at each node,
  split on the feature that most improves purity -- i.e. maximizes the impurity
  reduction (information gain / Gini gain). Choosing between two candidate splits
  by their gain is:

      choose-split gain-a feature-a gain-b feature-b
        = if gain-a <= gain-b then feature-b else feature-a

  (return the feature index of the higher-gain split), over exact-rational gains.
  Proved native and axiom-free: the split-selection rule; a worked split picking
  the higher-gain feature; the certificate that the chosen split's gain is at
  least the alternative's (native nnrat/at-most); and a stopping decision -- a
  node is a leaf when the best gain does not exceed the minimum-gain threshold.
  The impurity measure and candidate enumeration are executable; what is proved is
  the greedy split selection and the leaf-stopping decision.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.decision-tree`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- choose-split [ga fa gb fb]
  (function/app (function/const* 'decision-tree/choose-split []) ga fa gb fb))
(defn- is-leaf? [best-gain min-gain]
  (function/app (function/const* 'decision-tree/is-leaf? []) best-gain min-gain))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; choose-split ga fa gb fb = if ga <= gb then fb else fa  (higher-gain feature)
(def choose-split-spec
  {:name 'decision-tree/choose-split :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['ga nnrat] ['fa nat] ['gb nnrat] ['fb nat]]
                        (if-nat (decide-at-most 'ga 'gb) 'fb 'fa))})

;; is-leaf? best-gain min-gain = decide (best-gain <= min-gain)  (stop splitting)
(def is-leaf-spec
  {:name 'decision-tree/is-leaf? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['best-gain nnrat] ['min-gain nnrat]]
                        (decide-at-most 'best-gain 'min-gain))})

(def definition-specs [choose-split-spec is-leaf-spec])

;; Theorems -----------------------------------------------------------------

;; Feature 1 (gain 5) beats feature 0 (gain 2): split on feature 1.
(def picks-higher-gain-spec
  {:name 'decision-tree/picks-higher-gain :universes []
   :type (equality nat
                   (choose-split (whole 2) (data-nat 0) (whole 5) (data-nat 1))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (choose-split (whole 2) (data-nat 0)
                                      (whole 5) (data-nat 1)))})

;; Certificate: the chosen split's gain is at least the alternative (2 <= 5).
(def chosen-gain-is-best-spec
  {:name 'decision-tree/chosen-gain-is-best :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A node whose best gain (1) does not exceed the min-gain threshold (2) becomes
;; a leaf (stop splitting).
(def becomes-leaf-spec
  {:name 'decision-tree/becomes-leaf :universes []
   :type (equality bool (is-leaf? (whole 1) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-leaf? (whole 1) (whole 2)))})

;; A node with a strong best gain (5 > threshold 2) keeps splitting.
(def keeps-splitting-spec
  {:name 'decision-tree/keeps-splitting :universes []
   :type (equality bool (is-leaf? (whole 5) (whole 2))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-leaf? (whole 5) (whole 2)))})

(def theorem-specs
  [picks-higher-gain-spec chosen-gain-is-best-spec becomes-leaf-spec
   keeps-splitting-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-decision-tree
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
