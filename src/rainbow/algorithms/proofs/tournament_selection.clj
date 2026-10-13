(ns rainbow.algorithms.proofs.tournament-selection
  "AHoF O43 Genetic Algorithm -- tournament selection operator: from a sampled
  tournament of candidate fitnesses the fittest (maximum) entrant is selected to
  reproduce. Selection is the max-fold of the tournament's fitnesses:

      winner fitnesses = fold nnrat-max 0 fitnesses

  where the pairwise nnrat-max keeps the larger of two fitnesses using the
  decidable rational order. Proved: worked instances -- max 2 7 = 7, the
  tournament [3,7,2] selects 7, and the worked certificate 3 <= winner [3,7,2]
  (a native nnrat/at-most). The stochastic sampling of which candidates enter a
  tournament is an executable concern; what is proved here is the max-fold
  selection at these instances. That the winner dominates every entrant for all
  tournaments, and the selection pressure it gives the GA, are not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all carried by the D63
  checkpoint, as used by nearest_neighbor and the geometric-convergence bounds).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.tournament-selection`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat (function/app (function/const* 'data/List [type-level]) nnrat))
(def zero-rational (function/const* 'nnrat/zero []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; A self-contained documentation proposition for the if-data condition slot.
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))

;; nnrat-max l r = if (l <= r) then r else l
(defn- nnrat-max-term [l r]
  (if-value (decide-at-most l r) r l))

(defn- nnrat-max [l r]
  (function/app (function/const* 'tournament/nnrat-max []) l r))
(defn- winner [fitnesses]
  (function/app (function/const* 'tournament/winner []) fitnesses))

;; A proof of `nnrat/at-most a b` via the decidable comparison computing to true.
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; nnrat-max l r = if (l <= r) then r else l  (the larger of two fitnesses)
(def nnrat-max-spec
  {:name 'tournament/nnrat-max :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['l nnrat] ['r nnrat]] (nnrat-max-term 'l 'r))})

;; winner fitnesses = fold nnrat-max 0 fitnesses  (the fittest entrant)
(def winner-spec
  {:name 'tournament/winner :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value
   (function/lam
    [['fitnesses list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nnrat)
     zero-rational
     (function/lam
      [['head nnrat] ['tail list-nnrat] ['tail-winner nnrat]]
      (nnrat-max 'head 'tail-winner))
     'fitnesses))})

(def definition-specs [nnrat-max-spec winner-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- fitness-list [& elements]
  (reduce (fn [tail element]
            (function/app (function/const* 'data/cons [type-level])
                          nnrat element tail))
          (function/app (function/const* 'data/nil [type-level]) nnrat)
          (reverse elements)))

;; Pairwise: max keeps the larger fitness (7 over 2).
(def max-keeps-larger-spec
  {:name 'tournament/max-keeps-larger :universes []
   :type (equality nnrat (nnrat-max (whole 2) (whole 7)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (nnrat-max (whole 2) (whole 7)))})

;; A tournament of fitnesses [3,7,2] selects the fittest entrant, 7.
(def winner-example-spec
  {:name 'tournament/winner-example :universes []
   :type (equality nnrat
                   (winner (fitness-list (whole 3) (whole 7) (whole 2)))
                   (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (winner (fitness-list (whole 3) (whole 7) (whole 2))))})

;; Worked certificate: entrant 3 <= winner of [3,7,2].
(def winner-dominates-entrant-spec
  {:name 'tournament/winner-dominates-entrant :universes []
   :type (nnrat-at-most (whole 3)
                        (winner (fitness-list (whole 3) (whole 7) (whole 2))))
   :value (at-most-proof (whole 3)
                         (winner (fitness-list (whole 3) (whole 7)
                                               (whole 2))))})

(def theorem-specs
  [max-keeps-larger-spec winner-example-spec winner-dominates-entrant-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :tournament-selection
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
