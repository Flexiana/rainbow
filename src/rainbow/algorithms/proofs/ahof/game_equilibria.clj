(ns rainbow.algorithms.proofs.ahof.game-equilibria
  "Kochenderfer 'Algorithms for Decision Making' Ch.24-27 multi-agent equilibrium cores
  as higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog.

  FLAGSHIP (a genuine OR theorem, not a worked instance):

    D25.5 Markov-game / zero-sum Nash : the 2x2 MINIMAX INEQUALITY
        max_row min_col V  <=  min_col max_row V
      (the saddle-point / weak-duality direction of von Neumann's minimax theorem),
      assembled purely from the min/max lattice (min-lower, max-upper, at-most-min,
      at-most-max, transitivity).

  Plus the shared no-profitable-deviation property of the other equilibrium solvers:

    D26.3 POMG Nash (conditional plans) : equilibrium value >= any deviation
    D27.3 Dec-POMDP iterated best resp. : joint best-response value >= any deviation
    D24.9 level-k / hierarchical softmax : level-k value >= the response it improves on

  Native and axiom-free; chains nnrat-minmax on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))
(defn- min-lower-left [a b] (function/app (function/const* 'minmax/min-lower-left []) a b))
(defn- min-lower-right [a b] (function/app (function/const* 'minmax/min-lower-right []) a b))
(defn- max-upper-left [a b] (function/app (function/const* 'minmax/max-upper-left []) a b))
(defn- max-upper-right [a b] (function/app (function/const* 'minmax/max-upper-right []) a b))
(defn- at-most-min [lo x y p q] (function/app (function/const* 'minmax/at-most-min []) lo x y p q))
(defn- at-most-max [x y hi p q] (function/app (function/const* 'minmax/at-most-max []) x y hi p q))

;; ---- D25.5 maximin / minimax and the saddle-point inequality -----------------
;; row player maximizes its worst-case column; column player minimizes its best-case row
(def maximin-spec
  {:name 'game/maximin :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['v00 nnrat] ['v01 nnrat] ['v10 nnrat] ['v11 nnrat]]
                        (rmax (rmin 'v00 'v01) (rmin 'v10 'v11)))})

(def minimax-spec
  {:name 'game/minimax :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['v00 nnrat] ['v01 nnrat] ['v10 nnrat] ['v11 nnrat]]
                        (rmin (rmax 'v00 'v10) (rmax 'v01 'v11)))})

;; maximin <= minimax  (weak duality / saddle-point inequality)
(def minimax-inequality-spec
  {:name 'game/minimax-inequality :universes []
   :type (function/forall [['v00 nnrat] ['v01 nnrat] ['v10 nnrat] ['v11 nnrat]]
                          (at-most (function/app (function/const* 'game/maximin []) 'v00 'v01 'v10 'v11)
                                   (function/app (function/const* 'game/minimax []) 'v00 'v01 'v10 'v11)))
   :value (function/lam [['v00 nnrat] ['v01 nnrat] ['v10 nnrat] ['v11 nnrat]]
                        (let [a (rmin 'v00 'v01) b (rmin 'v10 'v11)
                              c (rmax 'v00 'v10) d (rmax 'v01 'v11)
                              a<=c (transitive a 'v00 c (min-lower-left 'v00 'v01) (max-upper-left 'v00 'v10))
                              a<=d (transitive a 'v01 d (min-lower-right 'v00 'v01) (max-upper-left 'v01 'v11))
                              b<=c (transitive b 'v10 c (min-lower-left 'v10 'v11) (max-upper-right 'v00 'v10))
                              b<=d (transitive b 'v11 d (min-lower-right 'v10 'v11) (max-upper-right 'v01 'v11))
                              a<=min (at-most-min a c d a<=c a<=d)
                              b<=min (at-most-min b c d b<=c b<=d)]
                          (at-most-max a b (rmin c d) a<=min b<=min)))})

;; ---- shared no-profitable-deviation solvers (max upper-bounds any deviation) --
(defn- br-value-def [nm]
  {:name nm :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['r0 nnrat] ['r1 nnrat]] (rmax 'r0 'r1))})

(defn- no-deviation-thm [nm def-nm]
  {:name nm :universes []
   :type (function/forall [['r0 nnrat] ['r1 nnrat]]
                          (at-most 'r0 (function/app (function/const* def-nm []) 'r0 'r1)))
   :value (function/lam [['r0 nnrat] ['r1 nnrat]] (max-upper-left 'r0 'r1))})

(def pomg-value-spec (br-value-def 'game/pomg-value))              ; D26.3
(def pomg-no-deviation-spec (no-deviation-thm 'game/pomg-no-deviation 'game/pomg-value))
(def dec-ibr-value-spec (br-value-def 'game/dec-ibr-value))        ; D27.3
(def dec-ibr-no-deviation-spec (no-deviation-thm 'game/dec-ibr-no-deviation 'game/dec-ibr-value))
(def levelk-value-spec (br-value-def 'game/levelk-value))          ; D24.9
(def levelk-no-deviation-spec (no-deviation-thm 'game/levelk-no-deviation 'game/levelk-value))

(def definition-specs
  [maximin-spec minimax-spec pomg-value-spec dec-ibr-value-spec levelk-value-spec])
(def theorem-specs
  [minimax-inequality-spec pomg-no-deviation-spec dec-ibr-no-deviation-spec
   levelk-no-deviation-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      minmax/extend-environment
      (support/extend-with :ahof-game-equilibria
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
