(ns rainbow.algorithms.proofs.minimax
  "AHoF adversarial decision-making -- the minimax value of a two-ply zero-sum
  game. The maximizing player chooses among moves; the adversary then chooses the
  worst (minimizing) reply to each. The value is the max over the player's moves
  of the min over the adversary's replies:

      value a b c d = max( min(a, b), min(c, d) )

  for a game where move 1 has replies (a, b) and move 2 has replies (c, d), the
  payoffs being exact nonnegative rationals. Both nnrat-min and nnrat-max use the
  decidable rational order. Proved: worked instances with replies (3,1) and
  (2,4) -- the minimax value is 2, and the worked certificates min(2,4) <= value
  and min(3,1) <= value. The game tree and move enumeration are executable
  concerns; what is proved here is the minimax combination at this instance. The
  classical security guarantee (committing to the best move secures at least the
  value against any reply) is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all carried by the D63
  checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.minimax`
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- nnrat-min-term [a b] (if-value (decide-at-most a b) a b))
(defn- nnrat-max-term [a b] (if-value (decide-at-most a b) b a))

(defn- value [a b c d]
  (function/app (function/const* 'minimax/value []) a b c d))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; value a b c d = max( min(a,b), min(c,d) )
(def value-spec
  {:name 'minimax/value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
                        (nnrat-max-term (nnrat-min-term 'a 'b)
                                        (nnrat-min-term 'c 'd)))})

(def definition-specs [value-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Move 1 has replies (3,1) -> guaranteed 1; move 2 has replies (2,4) ->
;; guaranteed 2. The maximizing player prefers move 2, so the value is 2.
(def value-example-spec
  {:name 'minimax/value-example :universes []
   :type (equality nnrat
                   (value (whole 3) (whole 1) (whole 2) (whole 4))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (value (whole 3) (whole 1) (whole 2) (whole 4)))})

;; Worked certificate: move 2's reply-minimum min(2,4) <= the minimax value.
(def value-secures-best-move-spec
  {:name 'minimax/value-secures-best-move :universes []
   :type (nnrat-at-most
          (nnrat-min-term (whole 2) (whole 4))
          (value (whole 3) (whole 1) (whole 2) (whole 4)))
   :value (at-most-proof
           (nnrat-min-term (whole 2) (whole 4))
           (value (whole 3) (whole 1) (whole 2) (whole 4)))})

;; Worked certificate: move 1's reply-minimum min(3,1) <= the minimax value.
(def value-dominates-other-move-spec
  {:name 'minimax/value-dominates-other-move :universes []
   :type (nnrat-at-most
          (nnrat-min-term (whole 3) (whole 1))
          (value (whole 3) (whole 1) (whole 2) (whole 4)))
   :value (at-most-proof
           (nnrat-min-term (whole 3) (whole 1))
           (value (whole 3) (whole 1) (whole 2) (whole 4)))})

(def theorem-specs
  [value-example-spec value-secures-best-move-spec
   value-dominates-other-move-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :minimax (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.minimax))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
